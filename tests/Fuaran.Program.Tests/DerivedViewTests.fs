/// A DERIVED VIEW is computed once per input value and journaled as derived
/// (Phase 2220, D47), pinned at the toy witness under the durable tier:
///
///   * **once per run**: a program reads a relation, derives an index over it,
///     and consults the index from several later steps — the view is computed
///     once, its input's content key is computed once, and the journal holds
///     ONE read and ONE derivation;
///   * **a replay shows it as derived**: the journal records the derivation
///     under `Derive`, keyed by the input's content, never as a second read;
///     a resume is served the read and the derivation and RECOMPUTES the view
///     from the served read — never from the moved world;
///   * **an unavailable input**: a view over an unavailable read is
///     unavailable, naming the read, computes nothing and journals nothing,
///     and the commit step refuses before anything is performed;
///   * **roadmap-engine#752's shapes on Program**: `cyclesAmong` and readiness over
///     redirects, stated over one derived index with no host machinery beyond
///     a one-line predicate.
module Fuaran.Program.Tests.DerivedViewTests

open Expecto
open Fuaran.Core
open Fuaran.Program
open Fuaran.Program.Bounded
open Fuaran.Program.Runtime
open Fuaran.Program.Server
open Fuaran.Program.Tests.ToyDomain

// ─── fixtures ────────────────────────────────────────────────────────────────

exception private ProcessDied of string

let private crashing (f: unit -> 'T) : bool =
    try
        f () |> ignore
        false
    with ProcessDied _ ->
        true

/// The two recursive questions the fixtures below ask of a relation, answered by their DEFINITIONS
/// (reachability by a worklist). The graph questions' one implementation is Core's
/// `Fuaran.Core.Relation` (Core D205); this repository takes no dependency on it for a test (D49), and
/// a fixture of a handful of nodes needs no linear pass.
module private Reach =

    let private successors (relation: Map<string, string list>) (node: string) =
        Map.tryFind node relation |> Option.defaultValue []

    /// Every node reached from `sources` by zero or more edges.
    let closure (relation: Map<string, string list>) (sources: string list) : Set<string> =
        let rec walk (seen: Set<string>) (pending: string list) =
            match pending with
            | [] -> seen
            | node :: rest when seen.Contains node -> walk seen rest
            | node :: rest -> walk (seen.Add node) (successors relation node @ rest)

        walk Set.empty sources

    /// The nodes that reach themselves by one or more edges.
    let cyclesAmong (relation: Map<string, string list>) : Set<string> =
        relation
        |> Map.keys
        |> Seq.filter (fun node -> (closure relation (successors relation node)).Contains node)
        |> Set.ofSeq

    /// Where a chain from `node` ends: the successor-less nodes it reaches, or `None` when it reaches a
    /// cycle and so never ends.
    let terminals (relation: Map<string, string list>) (node: string) : Set<string> option =
        let reached = closure relation [ node ]
        let onCycle = cyclesAmong relation

        if reached |> Set.exists onCycle.Contains then
            None
        else
            Some(reached |> Set.filter (fun n -> List.isEmpty (successors relation n)))

let private leaf id =
    { Id = id
      Label = Const(JStr "")
      Handlers = []
      Children = [] }

let private emptyStore: ServerStore<ToyNode, ToyStore> =
    { Tree =
        { Id = "root"
          Label = Const(JStr "root")
          Handlers = []
          Children = [ leaf "cycles"; leaf "ends"; leaf "status" ] }
      Bindings = Map.empty }

let private labelOf (id: string) (root: ToyNode) : string option =
    root.Children
    |> List.tryPick (fun n ->
        match n.Id, n.Label with
        | i, Const(JStr label) when i = id -> Some label
        | _ -> None)

let private relabel (id: string) (label: string) (root: ToyNode) : ToyNode =
    { root with
        Children =
            root.Children
            |> List.map (fun n ->
                if n.Id = id then
                    { n with Label = Const(JStr label) }
                else
                    n) }

let private freshJournal () =
    Journal.declaringDurable (Journal.inMemory ())

let private dyingBeforeAttempting (step: int) (inner: EffectJournal) : EffectJournal =
    { inner with
        Append =
            fun entry ->
                match entry.Phase with
                | JournalPhase.Attempted when entry.Step = step -> raise (ProcessDied "between steps")
                | _ -> inner.Append entry }

/// A relation as the store holds it: `a:b,c;b:;c:a` — each node and its
/// successors. The store's own codec reads it.
let private relationCodec: ReadCodec<Map<string, string list>> =
    { Name = "relation-v1"
      Decode =
        fun text ->
            text.Split(';', System.StringSplitOptions.RemoveEmptyEntries)
            |> Array.fold
                (fun acc entry ->
                    acc
                    |> Result.bind (fun (m: Map<string, string list>) ->
                        match entry.Split ':' with
                        | [| node; targets |] ->
                            Ok(
                                Map.add
                                    node
                                    (targets.Split(',', System.StringSplitOptions.RemoveEmptyEntries) |> List.ofArray)
                                    m
                            )
                        | _ -> Error("not an entry: " + entry)))
                (Ok Map.empty) }

/// A store holding one relation, which can be rewritten and made unreachable.
type private Store(initial: string) =
    let mutable content = initial
    let mutable reachable = true
    member _.Write(text: string) = content <- text
    member _.Unreachable() = reachable <- false

    member _.Read() : Result<string, string> =
        if reachable then
            Ok content
        else
            Error "the store is unreachable"

/// The index a program derives over the relation it read: cycle membership and
/// where every chain ends, from ONE pass each.
type private Index =
    { Cycles: Set<string>
      Ends: string -> Set<string> option }

/// The derived view, keyed by a content address of the relation's canonical
/// form. `keyed` counts how often the content key was computed.
let private indexView (name: string) (keyed: int ref) : DerivedView<Map<string, string list>, Index> =
    DerivedView.ofContent
        name
        (fun relation ->
            keyed.Value <- keyed.Value + 1

            relation
            |> Map.toList
            |> List.map (fun (n, ts) -> n + ":" + String.concat "," ts)
            |> String.concat ";")
        (fun relation ->
            { Cycles = Reach.cyclesAmong relation
              Ends = Reach.terminals relation })

let private readMarker = "@read"
let private cyclesMarker = "@cycles"
let private endsMarker = "@ends:"
let private commitMarker = "@commit"

/// The toy witness whose plan reads the relation once (`@read`), consults the
/// derived index from two later steps (`@cycles`, `@ends:<node>`), and refuses
/// at `@commit` on the run's unavailable reads. The read value is HELD by the
/// plan between steps, as a program's value is.
let private derivingWitness (store: Store) (view: DerivedView<Map<string, string list>, Index>) =
    fun (reader: EntryReader) (recorder: DerivationRecorder) (ledger: (Reads * Derivations) option ref) ->
        let reads = Reads.Over reader
        let derivations = Derivations.Over recorder
        ledger.Value <- Some(reads, derivations)
        let mutable held: Read<Map<string, string list>> option = None

        let index () =
            match held with
            | None -> Error "the plan consulted the index before it read the relation"
            | Some read -> derivations.OfRead(view, read)

        { witness with
            State =
                { witness.State with
                    Stream =
                        { witness.State.Stream with
                            Apply =
                                fun op tree ->
                                    match op with
                                    | Relabel(id, label) when label = readMarker ->
                                        reads.Read(relationCodec, "relation", store.Read)
                                        |> Result.map (fun read ->
                                            held <- Some read
                                            tree)
                                    | Relabel(id, label) when label = cyclesMarker ->
                                        index ()
                                        |> Result.map (fun ix ->
                                            match ix with
                                            | Read.Available ix -> relabel id (String.concat "," ix.Cycles) tree
                                            | Read.Unavailable _ -> tree)
                                    | Relabel(id, label) when label.StartsWith endsMarker ->
                                        index ()
                                        |> Result.map (fun ix ->
                                            match ix with
                                            | Read.Available ix ->
                                                match ix.Ends(label.Substring endsMarker.Length) with
                                                | Some ends -> relabel id (String.concat "," ends) tree
                                                | None -> relabel id "loops" tree
                                            | Read.Unavailable _ -> tree)
                                    | Relabel(id, label) when label = commitMarker ->
                                        match reads.Refusal() with
                                        | Some refusal -> Error refusal
                                        | None -> Ok(relabel id "Committed" tree)
                                    | Relabel(id, label) -> Ok(relabel id label tree) } } }

/// Read once; consult the derived index from three steps; commit; audit.
let private handler: Handler<ToyAction, ToyOp> =
    { Name = "index"
      Stages =
        [ Effect(ServerEffect.ApplyOps [ Relabel("status", readMarker) ])
          Effect(ServerEffect.ApplyOps [ Relabel("cycles", cyclesMarker) ])
          Effect(ServerEffect.ApplyOps [ Relabel("ends", endsMarker + "a") ])
          Effect(ServerEffect.ApplyOps [ Relabel("ends", endsMarker + "x") ])
          Effect(ServerEffect.ApplyOps [ Relabel("status", commitMarker) ])
          Effect(ServerEffect.HostCall("audit", JStr "committed", None)) ] }

let private run (store: Store) view journal (audits: int ref) ledger =
    Durable.runDeriving
        (fun reader recorder -> derivingWitness store view reader recorder ledger)
        (DurableServices.create |> DurableServices.withJournal journal)
        "inv"
        (ServerEffectRegistry.denyAll
         |> ServerEffectRegistry.register "audit" (fun _ ->
             audits.Value <- audits.Value + 1
             Ok(JStr "recorded"))
         |> ServerEffectRegistry.permissive)
        OpPerformance.InMemory
        Fuaran.Compute.DataFrame.noResolve
        "node"
        handler
        emptyStore

let private capabilities (journal: EffectJournal) =
    journal.Read "inv"
    |> List.filter (fun e -> e.Phase = JournalPhase.Attempted)
    |> List.map (fun e -> e.Step, e.Capability)

// a -> b -> c, c -> a: a cycle; x -> y -> z, x -> w: chains ending at z and w.
let private cyclic = "a:b;b:c;c:a;x:y,w;y:z"
let private acyclic = "a:b;b:c;c:;x:y,w;y:z"

// ─── once per run, and journaled as derived ──────────────────────────────────

let private once =
    testList
        "a program derives a view once from a read and consults it from several steps"
        [ test "three steps consult the index; it is computed once, keyed once, and journaled once as derived" {
              let keyed = ref 0
              let journal = freshJournal ()
              let ledger = ref None
              let outcome = run (Store cyclic) (indexView "index" keyed) journal (ref 0) ledger

              Expect.isTrue outcome.Outcome.Committed "the run committed"
              let tree = outcome.Outcome.Store.Tree
              Expect.equal (labelOf "cycles" tree) (Some "a,b,c") "cyclesAmong, through the derived index"
              Expect.equal (labelOf "ends" tree) (Some "w,z") "the last step's chain ends, from the same index"

              let _, derivations = ledger.Value.Value
              Expect.equal derivations.Computations 1 "three consults, one computation"
              Expect.equal keyed.Value 1 "and one content key: the second and third consult hashed nothing"

              Expect.equal
                  (capabilities journal)
                  [ 0, Durable.EntryReadCapability; 1, Durable.DeriveCapability; 2, "host:audit" ]
                  "one read, one derivation — never a second read — and the host call"

              Expect.equal
                  (Durable.derivations journal "inv")
                  (Ok derivations.Derived)
                  "the journal alone shows what the run derived, keyed by its input"

              Expect.isTrue
                  (derivations.Derived.Head.Input.StartsWith ProgramWire.ContentAddressPrefix)
                  "the key is the input's content address"
          }

          test "equal inputs share one computation; a different input is a second" {
              let keyed = ref 0
              let view = indexView "index" keyed
              let derivations = Derivations.Over DerivationRecorder.live

              let parse text =
                  relationCodec.Decode text |> Result.toOption |> Option.get

              let first = derivations.Of(view, parse cyclic)
              let again = derivations.Of(view, parse cyclic)
              let other = derivations.Of(view, parse acyclic)

              Expect.equal (first |> Result.map _.Cycles) (Ok(Set.ofList [ "a"; "b"; "c" ])) "the cycle"
              Expect.equal (again |> Result.map _.Cycles) (first |> Result.map _.Cycles) "the same view"
              Expect.equal (other |> Result.map _.Cycles) (Ok Set.empty) "the other relation's"
              Expect.equal derivations.Computations 2 "two contents, two computations"
              Expect.equal keyed.Value 3 "three objects, three keys: a value equal by content shares the computation"
          }

          test "one view name asked at two value types is the tier's refusal, never a cast" {
              let derivations = Derivations.Over DerivationRecorder.live
              let asCount = DerivedView.ofContent "v" id String.length
              let asText = DerivedView.ofContent "v" id (fun (s: string) -> s.ToUpperInvariant())
              Expect.equal (derivations.Of(asCount, "abc")) (Ok 3) "the first"
              Expect.isError (derivations.Of(asText, "abc")) "the second is refused"
          } ]

// ─── replay ──────────────────────────────────────────────────────────────────

let private replay =
    testList
        "a replay shows the view as derived and recomputes it from the served read"
        [ test "a resume is served the read and the derivation, and its index is the dead run's, not the moved world's" {
              let store = Store cyclic
              let journal = freshJournal ()

              let died =
                  crashing (fun () ->
                      run store (indexView "index" (ref 0)) (dyingBeforeAttempting 2 journal) (ref 0) (ref None))

              Expect.isTrue died "the process died at the host call's attempt"
              store.Write acyclic

              let audits = ref 0
              let ledger = ref None
              let resumed = run store (indexView "index" (ref 0)) journal audits ledger

              Expect.isTrue resumed.Outcome.Committed "the resumed run committed"
              Expect.equal resumed.Replayed [ 0; 1 ] "the read and the derivation were served"
              Expect.equal resumed.Invoked [ 2 ] "only the host call reached the world"
              Expect.equal audits.Value 1 "exactly once"

              Expect.equal
                  (labelOf "cycles" resumed.Outcome.Store.Tree)
                  (Some "a,b,c")
                  "the index over what the dead run READ — the moved world has no cycle"

              let _, derivations = ledger.Value.Value
              Expect.equal derivations.Computations 1 "recomputed once, from the served read"

              Expect.equal
                  (Durable.derivations journal "inv" |> Result.map List.length)
                  (Ok 1)
                  "still one derivation in the trace"
          }

          test "a resume that would derive another view at the derivation's ordinal is refused, not served" {
              let journal = freshJournal ()

              crashing (fun () ->
                  run (Store cyclic) (indexView "index" (ref 0)) (dyingBeforeAttempting 2 journal) (ref 0) (ref None))
              |> ignore

              let audits = ref 0

              let resumed =
                  run (Store cyclic) (indexView "index-v2" (ref 0)) journal audits (ref None)

              Expect.isFalse resumed.Outcome.Committed "the replay diverged"

              Expect.equal
                  resumed.Outcome.Diagnostics
                  [ ServerDiagnostic.Failed("ApplyOps", DurableCode.ReplayDivergence) ]
                  "the recorded derivation is not served to another view"

              Expect.equal audits.Value 0 "nothing was performed"
          } ]

// ─── an unavailable input ────────────────────────────────────────────────────

let private unavailable =
    testList
        "a view over an unavailable read is unavailable and computes nothing"
        [ test
              "the view answers Unavailable naming the read; nothing is derived or journaled as derived; commit refuses" {
              let store = Store cyclic
              store.Unreachable()
              let journal = freshJournal ()
              let audits = ref 0
              let ledger = ref None
              let outcome = run store (indexView "index" (ref 0)) journal audits ledger

              Expect.isFalse outcome.Outcome.Committed "the run did not commit"

              Expect.equal
                  outcome.Outcome.Diagnostics
                  [ ServerDiagnostic.Failed(
                        "ApplyOps",
                        "read-unavailable: relation (not-read: the store is unreachable)"
                    ) ]
                  "the commit step's refusal names the read the view could not be derived from"

              let _, derivations = ledger.Value.Value
              Expect.equal derivations.Computations 0 "no view was computed over nothing"
              Expect.isEmpty derivations.Derived "and nothing was derived"
              Expect.equal (capabilities journal) [ 0, Durable.EntryReadCapability ] "the read alone was journaled"
              Expect.equal audits.Value 0 "the host call never ran"
          }

          test "OfRead passes the read's own reason through" {
              let derivations = Derivations.Over DerivationRecorder.live

              let why =
                  { Subject = "relation"
                    Cause = ReadCause.NotRead "gone" }

              Expect.equal
                  (derivations.OfRead(indexView "index" (ref 0), Read.Unavailable why)
                   |> Result.map (Read.map _.Cycles))
                  (Ok(Read.Unavailable why))
                  "unavailable for the same reason, naming the same read"
          } ]

// ─── roadmap-engine#752's shapes, stated on Program ───────────────────────────────

/// A roadmap-shaped value: each phase's dependencies, the phases a superseded
/// phase's work was carried into, and which phases shipped.
type private Plan =
    { Deps: Map<string, string list>
      Carried: Map<string, string list>
      Shipped: Set<string> }

/// ONE index per plan, derived once: the dependency cycles and where each
/// carried phase's work finally lands.
type private PlanIndex =
    { DepCycles: Set<string>
      Survivors: string -> Set<string> option }

let private planView: DerivedView<Plan, PlanIndex> =
    { Name = "plan-index"
      Key = fun plan -> sprintf "%A" (plan.Deps, plan.Carried, plan.Shipped)
      Derive =
        fun plan ->
            { DepCycles = Reach.cyclesAmong plan.Deps
              Survivors = Reach.terminals plan.Carried } }

/// Readiness over redirects, roadmap-engine#752's one predicate, as a host states it on
/// Program: not shipped, not itself carried away, and every dependency either
/// shipped or carried into survivors that have all shipped (or are the
/// dependant itself, which has absorbed the work). A loop of carries has no
/// survivor and never reads ready.
let private ready (plan: Plan) (ix: PlanIndex) (phase: string) : bool =
    let satisfied dep =
        plan.Shipped.Contains dep
        || (plan.Carried.ContainsKey dep
            && match ix.Survivors dep with
               | Some survivors -> survivors |> Set.forall (fun s -> s = phase || plan.Shipped.Contains s)
               | None -> false)

    not (plan.Shipped.Contains phase)
    && not (plan.Carried.ContainsKey phase)
    && (Map.tryFind phase plan.Deps |> Option.defaultValue [] |> List.forall satisfied)

let private consumer =
    testList
        "roadmap-engine#752's shapes are stated on Program with no host machinery"
        [ test "cyclesAmong and readiness over redirects, from one derived index consulted per phase" {
              let plan =
                  { Deps =
                      Map.ofList
                          [ "p1", []
                            "p2", [ "p1" ]
                            "p3", [ "old" ]
                            "p4", [ "gone" ]
                            "p5", [ "loop1" ]
                            "p6", [ "fan" ]
                            "q1", [ "q2" ]
                            "q2", [ "q1" ] ]
                    Carried =
                      Map.ofList
                          [ "old", [ "mid" ]
                            "mid", [ "p1" ] // old -> mid -> p1 (shipped): satisfied
                            "gone", [ "p9" ] // carried into an unshipped survivor
                            "loop1", [ "loop2" ]
                            "loop2", [ "loop1" ] // a loop of carries: no survivor
                            "fan", [ "p6"; "p1" ] ] // carried into p6 itself and p1: absorbed
                    Shipped = Set.ofList [ "p1" ] }

              let derivations = Derivations.Over DerivationRecorder.live
              let phases = plan.Deps |> Map.toList |> List.map fst

              // Every phase's readiness consults the index; the index is derived once.
              let readiness =
                  phases
                  |> List.map (fun p -> p, derivations.Of(planView, plan) |> Result.map (fun ix -> ready plan ix p))

              Expect.equal
                  (derivations.Of(planView, plan) |> Result.map _.DepCycles)
                  (Ok(Set.ofList [ "q1"; "q2" ]))
                  "cyclesAmong over the dependency relation: RM-DEP-CYCLE's set"

              Expect.equal
                  (readiness |> List.choose (fun (p, r) -> if r = Ok true then Some p else None))
                  [ "p2"; "p3"; "p6" ]
                  "ready: a shipped dep, a chain of carries ending shipped, a dependant that absorbed the work"

              Expect.equal derivations.Computations 1 "eight phases judged over one index"
          } ]

[<Tests>]
let tests =
    testList
        "Phase 2220 - a derived view computed once per input value, journaled as derived"
        [ once; replay; unavailable; consumer ]
