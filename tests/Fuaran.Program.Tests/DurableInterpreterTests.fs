/// The durable interpreter at the TOY witness — what Phase 2165 (D39) added to
/// it, pinned against production:
///
///   * **the plan's entry read** (F-ENTRY): a plan that reads the world through
///     the run's `EntryReader` is journaled at its ordinal under `ReadEntry`,
///     and a re-entry of the same invocation is SERVED what the dead run's
///     entry saw — so a run killed after the op that MOVED what it read, and
///     before the stage after it, resumes against the record, stages the same
///     calls, serves the op and performs only the rest. The first case is the
///     reproduction the phase asked for first: the same interruption under a
///     witness that reads LIVE re-plans against the moved world and is refused
///     by the domain before any stage, with the stage after the op never
///     reached — the finding as it was reported on 0.7.1. A resume whose plan
///     would read another subject at that ordinal, or reach a stage where the
///     record holds a read, is refused under `durable-entry-read-diverged`
///     naming the read, never as the domain's own "nothing matched".
///   * **a plan-phase act** (Phase 2222, D63): a plan that ACTS without reading
///     — a wait between two peeks, a fold-first merge an entry read then reads
///     — through the run's `PlanActor` is journaled at its ordinal under
///     `PlanAct`, and a resume is served its answer and does not act again; a
///     resume that would act differently is refused under
///     `durable-plan-act-diverged` naming the act, and a live placement acts
///     every time it plans.
///   * **the run's prefix at the performer and the contract** (F-RECEIPTS): the
///     pre-op state and the receipts of the earlier op stages, in perform
///     order — a served stage's recorded receipt among them on a resume.
///   * **an idempotency facet per effect kind** (F-FACET): the kinds an op's
///     reach names, met per op, so a crash inside a write closes its window by
///     re-invoking while one inside a push is refused, under one declaration.
///   * **contracts composed by Program** (F-CONTRACTS): a list, checked in
///     order, the first that rejects naming the refusal.
module Fuaran.Program.Tests.DurableInterpreterTests

open Expecto
open Fuaran.Core
open Fuaran.Program.Bounded
open Fuaran.Program.Runtime
open Fuaran.Program.Server
open Fuaran.Program.Tests.ToyDomain
open Fuaran.Program.Tests.ToyDurableReplayTests

// ─── fixtures ────────────────────────────────────────────────────────────────
//
// The process killer, the base tree and store, the registry and the journals
// are `ToyDurableReplayTests`'s, shared rather than copied.


let private labelOf (id: string) (root: ToyNode) : string option =
    let rec go (n: ToyNode) =
        if n.Id = id then
            match n.Label with
            | Const(JStr label) -> Some label
            | _ -> None
        else
            n.Children |> List.tryPick go

    go root

let private relabel (id: string) (label: string) (root: ToyNode) : ToyNode =
    let rec go (n: ToyNode) =
        if n.Id = id then
            { n with Label = Const(JStr label) }
        else
            { n with
                Children = n.Children |> List.map go }

    go root

let private counting (count: int ref) (answer: string) =
    fun (_: JVal) ->
        count.Value <- count.Value + 1
        Ok(JStr answer)

let private run
    (witnessOf: EntryReader -> FullWitness<ToyNode, ToyAction, ToyExpr, ToyStore, ToyOp, ToyEffect>)
    (services: DurableServices)
    (invocation: string)
    (registry: ServerEffectRegistry)
    (performance: OpPerformance<ToyNode, ToyOp>)
    (handler: Handler<ToyAction, ToyOp>)
    =
    Durable.runReading
        witnessOf
        services
        invocation
        registry
        performance
        Fuaran.Compute.DataFrame.noResolve
        "node"
        handler
        emptyStore

// ─── the world a plan reads ──────────────────────────────────────────────────

/// A world the plan reads and the op performer moves: keyed slots.
type private World() =
    let slots = System.Collections.Generic.Dictionary<string, string>()
    member _.Set(key: string, value: string) = slots[key] <- value
    member _.Remove(key: string) = slots.Remove key |> ignore
    member _.Holds(key: string) = slots.ContainsKey key

    /// The live read, as the host encodes it for the journal: the slot's value,
    /// or the empty object for a slot the world no longer holds.
    member _.Read(key: string) : Result<JVal, string> =
        match slots.TryGetValue key with
        | true, value -> Ok(JStr value)
        | _ -> Ok(JObj [])

/// The marker a label carries to say "read this slot of the world at plan
/// time": `Relabel(id, "@world:<slot>")` relabels `id` with what the world
/// holds under `<slot>`, and is refused by the domain — as the domain's own
/// `no-match` — when the world no longer holds it. That is the shape the
/// finding described: a plan that reads a value its own op will move.
let private readingMarker = "@world:"

let private slotOf (label: string) : string option =
    if label.StartsWith readingMarker then
        Some(label.Substring readingMarker.Length)
    else
        None

/// The toy witness whose `Apply` reads the world through `reader` — the host's
/// part of the entry read: the subject is the slot's name, the live read is
/// the world's, and the served value is decoded by the same `Apply`.
let private readingWitness (world: World) (reader: EntryReader) =
    { witness with
        State =
            { witness.State with
                Stream =
                    { witness.State.Stream with
                        Apply =
                            fun op tree ->
                                match op with
                                | Relabel(id, label) ->
                                    match slotOf label with
                                    | None -> Ok(relabel id label tree)
                                    | Some slot ->
                                        match reader slot (fun () -> world.Read slot) with
                                        | Error reason -> Error reason
                                        | Ok(JStr value) -> Ok(relabel id value tree)
                                        | Ok _ -> Error("no-match: the world holds no " + slot) } } }

/// The witness that reads LIVE whatever interpreter runs it — a host that has
/// not adopted `runReading`, which is every host before this phase.
let private liveReadingWitness (world: World) =
    fun (_: EntryReader) -> readingWitness world EntryReader.live

/// The handler the finding describes: ONE op whose plan reads the slot and
/// whose performance retires it, then a host call — so the stage after the op
/// is what an interruption between the two leaves undone.
let private readThenRetireThenAudit: Handler<ToyAction, ToyOp> =
    { Name = "retire"
      Stages =
        [ Effect(ServerEffect.ApplyOps [ Relabel("title", readingMarker + "bundle") ])
          Effect(ServerEffect.HostCall("audit", JStr "retired", None)) ] }

/// The same handler reading ANOTHER slot — the resume that would plan
/// differently.
let private readOtherThenAudit: Handler<ToyAction, ToyOp> =
    { Name = "retire-other"
      Stages =
        [ Effect(ServerEffect.ApplyOps [ Relabel("title", readingMarker + "other") ])
          Effect(ServerEffect.HostCall("audit", JStr "retired", None)) ] }

/// A handler that reads nothing at its first call — an op stage where the
/// record holds the read.
let private noReadThenAudit: Handler<ToyAction, ToyOp> =
    { Name = "no-read"
      Stages =
        [ Effect(ServerEffect.ApplyOps [ Relabel("title", "Edited") ])
          Effect(ServerEffect.HostCall("audit", JStr "retired", None)) ] }

/// The op performer the finding describes: performing the op MOVES what the
/// plan read — the slot is retired from the world — and answers the label it
/// landed as its receipt.
let private retiring (world: World) (performed: int ref) : OpPerformance<ToyNode, ToyOp> =
    OpPerformance.performedWithDetail (fun state op ->
        performed.Value <- performed.Value + 1

        match op with
        | Relabel(id, _) ->
            world.Remove "bundle"
            Ok(JStr(labelOf id state |> Option.defaultValue "")))

/// The whole interruption: the world holds the bundle, the run reads it, the
/// op retires it and is journaled, and the process dies at the host call's
/// attempt. Answers the journal the death left and what the dead run's plan
/// read.
let private interruptedOver (journal: EffectJournal) =
    let world = World()
    world.Set("bundle", "Live")
    let audits = ref 0
    let performed = ref 0

    let died =
        crashing (fun () ->
            run
                (readingWitness world)
                (DurableServices.create
                 |> DurableServices.withJournal (dyingBeforeAttempting 2 journal))
                "inv"
                (registryOf [ "audit", counting audits "recorded" ])
                (retiring world performed)
                readThenRetireThenAudit)

    Expect.isTrue died "the fixture's process died at the host call's attempt"
    Expect.equal performed.Value 1 "the op performed before the death"
    Expect.equal audits.Value 0 "the host call never reached the world"
    Expect.isFalse (world.Holds "bundle") "the op MOVED what the plan read"
    world

/// The interruption over a fresh in-memory journal, answering both.
let private interrupted () =
    let journal = freshJournal ()
    interruptedOver journal, journal

// ─── F-ENTRY ─────────────────────────────────────────────────────────────────

let private entryRead =
    testList
        "the plan's entry read (F-ENTRY)"
        [ test
              "premise: under a live-reading witness the resume re-plans against the moved world and is refused before any stage — the finding as reported" {
              let world, journal = interrupted ()
              let audits = ref 0
              let performed = ref 0

              let resumed =
                  run
                      (liveReadingWitness world)
                      (DurableServices.create |> DurableServices.withJournal journal)
                      "inv"
                      (registryOf [ "audit", counting audits "recorded" ])
                      (retiring world performed)
                      readThenRetireThenAudit

              Expect.isFalse resumed.Outcome.Committed "the resume did not commit"

              Expect.equal
                  resumed.Outcome.Diagnostics
                  [ ServerDiagnostic.Failed("ApplyOps", "no-match: the world holds no bundle") ]
                  "the domain's own refusal, from the plan phase, naming nothing about the resume"

              Expect.equal performed.Value 0 "the journaled op stage was never reached"
              Expect.equal audits.Value 0 "the stage after it stays undone: the host call never ran"
              Expect.isEmpty resumed.Replayed "nothing was served"
          }

          test
              "the entry read is journaled at its ordinal: ReadEntry, the slot as subject, what the world answered as its value" {
              let world = World()
              world.Set("bundle", "Live")
              let journal = freshJournal ()

              let outcome =
                  run
                      (readingWitness world)
                      (DurableServices.create |> DurableServices.withJournal journal)
                      "inv"
                      (registryOf [ "audit", fun _ -> Ok(JStr "recorded") ])
                      (retiring world (ref 0))
                      readThenRetireThenAudit

              Expect.isTrue outcome.Outcome.Committed "the run committed"
              Expect.equal outcome.Invoked [ 0; 1; 2 ] "the read, the op stage and the host call, in one sequence"

              let entries = journal.Read "inv" |> List.filter (fun e -> e.Step = 0)

              Expect.equal
                  entries
                  [ { Invocation = "inv"
                      Step = 0
                      Capability = Durable.EntryReadCapability
                      Subject = Some "bundle"
                      Phase = JournalPhase.Attempted }
                    { Invocation = "inv"
                      Step = 0
                      Capability = Durable.EntryReadCapability
                      Subject = Some "bundle"
                      Phase = JournalPhase.Completed(JStr "Live") } ]
                  "attempted, then completed with the value the world answered"

              Expect.equal
                  (labelOf "title" outcome.Outcome.Store.Tree)
                  (Some "Live")
                  "the plan relabelled with what it read"
          }

          test
              "killed between the op and the host call, a FRESH file store serves the dead run's entry read and its op stage (Phase 2589)" {
              withDirectory (fun directory ->
                  let world = interruptedOver (JournalStore.file directory).Journal
                  let store = JournalStore.file directory
                  let audits = ref 0
                  let performed = ref 0

                  let resumed =
                      run
                          (readingWitness world)
                          (DurableServices.create |> DurableServices.withStore store)
                          "inv"
                          (registryOf [ "audit", counting audits "recorded" ])
                          (retiring world performed)
                          readThenRetireThenAudit

                  Expect.isTrue resumed.Outcome.Committed "the resumed run committed"
                  Expect.equal resumed.Replayed [ 0; 1 ] "the entry read and the op stage were served from disk"
                  Expect.equal performed.Value 0 "the op was not performed a second time"
                  Expect.equal audits.Value 1 "the host call reached the world exactly once"

                  Expect.equal
                      (labelOf "title" resumed.Outcome.Store.Tree)
                      (Some "Live")
                      "the resumed plan relabelled with what the DEAD process read"

                  Expect.equal (store.Close "inv") (Ok()) "the completed run closes")
          }

          test
              "resumed under runReading, the plan observes the journaled entry: the op is served, only the host call reaches the world, and the run commits" {
              let world, journal = interrupted ()
              let audits = ref 0
              let performed = ref 0

              let resumed =
                  run
                      (readingWitness world)
                      (DurableServices.create |> DurableServices.withJournal journal)
                      "inv"
                      (registryOf [ "audit", counting audits "recorded" ])
                      (retiring world performed)
                      readThenRetireThenAudit

              Expect.isTrue resumed.Outcome.Committed "the resumed run committed"
              Expect.equal resumed.Replayed [ 0; 1 ] "the entry read and the op stage were served"
              Expect.equal resumed.Invoked [ 2 ] "only the host call was invoked"
              Expect.isEmpty resumed.Indeterminate "nothing was undecided"
              Expect.equal performed.Value 0 "the op was not performed a second time"
              Expect.equal audits.Value 1 "the host call reached the world exactly once"

              Expect.equal
                  (labelOf "title" resumed.Outcome.Store.Tree)
                  (Some "Live")
                  "the resumed plan relabelled with what the DEAD run read, not with the moved world"

              Expect.equal
                  resumed.Outcome.Performed
                  [ "ApplyOps"; "host:audit" ]
                  "the audit trail is the uninterrupted run's: the op stage once, then the host call"

              let attempts =
                  journal.Read "inv"
                  |> List.filter (fun e -> e.Phase = JournalPhase.Attempted)
                  |> List.countBy _.Step

              Expect.all attempts (fun (_, n) -> n = 1) "no step was attempted twice"
          }

          test
              "a fresh invocation against the moved world reads live and is refused by the domain: the record is the invocation's, never the world's" {
              let world, _ = interrupted ()

              let fresh =
                  run
                      (readingWitness world)
                      (DurableServices.create |> DurableServices.withJournal (freshJournal ()))
                      "another"
                      (registryOf [ "audit", fun _ -> Ok(JStr "recorded") ])
                      (retiring world (ref 0))
                      readThenRetireThenAudit

              Expect.isFalse fresh.Outcome.Committed "a new invocation sees the world as it is"

              Expect.equal
                  fresh.Outcome.Diagnostics
                  [ ServerDiagnostic.Failed("ApplyOps", "no-match: the world holds no bundle") ]
                  "and is refused by the domain"
          }

          test
              "a resume whose plan reads ANOTHER subject at the read's ordinal is refused naming the read, before any stage" {
              let world, journal = interrupted ()
              let audits = ref 0
              let performed = ref 0

              let resumed =
                  run
                      (readingWitness world)
                      (DurableServices.create |> DurableServices.withJournal journal)
                      "inv"
                      (registryOf [ "audit", counting audits "recorded" ])
                      (retiring world performed)
                      readOtherThenAudit

              Expect.isFalse resumed.Outcome.Committed "refused"

              Expect.equal
                  resumed.Outcome.Diagnostics
                  [ ServerDiagnostic.Failed("ApplyOps", DurableCode.entryReadDiverged "other") ]
                  "the typed refusal names the read the resumed plan would make"

              Expect.equal performed.Value 0 "no stage was reached"
              Expect.equal audits.Value 0 "no stage was reached"
          }

          test
              "a resume whose plan reaches an op stage where the record holds the read is refused naming the recorded read" {
              let world, journal = interrupted ()
              let audits = ref 0
              let performed = ref 0

              let resumed =
                  run
                      (readingWitness world)
                      (DurableServices.create |> DurableServices.withJournal journal)
                      "inv"
                      (registryOf [ "audit", counting audits "recorded" ])
                      (retiring world performed)
                      noReadThenAudit

              Expect.isFalse resumed.Outcome.Committed "refused"

              Expect.equal
                  resumed.Outcome.Diagnostics
                  [ ServerDiagnostic.PerformFailed("ApplyOps", DurableCode.entryReadDiverged "bundle") ]
                  "the refusal names the read the dead run made where this plan performs"

              Expect.equal performed.Value 0 "the op was not performed"
              Expect.equal audits.Value 0 "the host call was not reached"
          }

          test
              "runWith is runReading over a witness that ignores the reader: a plan that reads nothing journals no read" {
              let journal = freshJournal ()

              let outcome =
                  Durable.runWith
                      witness
                      (DurableServices.create |> DurableServices.withJournal journal)
                      "inv"
                      (registryOf [ "audit", fun _ -> Ok(JStr "recorded") ])
                      (OpPerformance.performedWithoutReceipt (fun _ _ -> Ok()))
                      Fuaran.Compute.DataFrame.noResolve
                      "node"
                      noReadThenAudit
                      emptyStore

              Expect.isTrue outcome.Outcome.Committed "committed"

              Expect.isFalse
                  (journal.Read "inv"
                   |> List.exists (fun e -> e.Capability = Durable.EntryReadCapability))
                  "no ReadEntry step"

              Expect.equal outcome.Invoked [ 0; 1 ] "the op stage and the host call, from ordinal zero"
          } ]

// ─── a plan-phase ACT (Phase 2222, D63) ──────────────────────────────────────
//
// The plane probe's two instances of one missing arm: a wait that peeks a
// queue, SLEEPS and peeks again, and a fold-first merge an entry read then
// reads. The toy's stand-ins: the marker `@act:<name>` performs the named act
// through the run's `PlanActor` and relabels with what the act answered (a
// non-string answer leaves the tree as it was); `@world:<slot>` reads as
// above.

let private actingMarker = "@act:"

let private actOf (label: string) : string option =
    if label.StartsWith actingMarker then
        Some(label.Substring actingMarker.Length)
    else
        None

/// The toy witness whose `Apply` reads the world through the plan's reader and
/// performs acts through the plan's actor — `acts` is the host's own table of
/// what each act does.
let private actingWitness (world: World) (plan: PlanRecorders) (acts: Map<string, unit -> Result<JVal, string>>) =
    { witness with
        State =
            { witness.State with
                Stream =
                    { witness.State.Stream with
                        Apply =
                            fun op tree ->
                                match op with
                                | Relabel(id, label) ->
                                    match slotOf label, actOf label with
                                    | Some slot, _ ->
                                        match plan.Read slot (fun () -> world.Read slot) with
                                        | Error reason -> Error reason
                                        | Ok(JStr value) -> Ok(relabel id value tree)
                                        | Ok _ -> Error("no-match: the world holds no " + slot)
                                    | None, Some name ->
                                        match Map.tryFind name acts with
                                        | None -> Error("no-act: " + name)
                                        | Some act ->
                                            match plan.Act name act with
                                            | Error reason -> Error reason
                                            | Ok(JStr answer) -> Ok(relabel id answer tree)
                                            | Ok _ -> Ok tree
                                    | None, None -> Ok(relabel id label tree) } } }

let private runPlanning
    (witnessOf: PlanRecorders -> FullWitness<ToyNode, ToyAction, ToyExpr, ToyStore, ToyOp, ToyEffect>)
    (services: DurableServices)
    (registry: ServerEffectRegistry)
    (handler: Handler<ToyAction, ToyOp>)
    =
    Durable.runPlanning
        witnessOf
        services
        "inv"
        registry
        OpPerformance.InMemory
        Fuaran.Compute.DataFrame.noResolve
        "node"
        handler
        emptyStore

/// One ApplyOps stage of three relabels, then the host call.
let private threeThenAudit (name: string) (title: string) (footer: string) (again: string) =
    { Name = name
      Stages =
        [ Effect(ServerEffect.ApplyOps [ Relabel("title", title); Relabel("footer", footer); Relabel("title", again) ])
          Effect(ServerEffect.HostCall("audit", JStr "waited", None)) ] }

/// The gate wait: peek the gate, pause, peek again, then the host call.
let private peekPausePeek: Handler<ToyAction, ToyOp> =
    threeThenAudit "wait" (readingMarker + "gate") (actingMarker + "pause") (readingMarker + "gate")

/// The same wait performing ANOTHER act where the recorded run paused.
let private peekFetchPeek: Handler<ToyAction, ToyOp> =
    threeThenAudit "wait-fetch" (readingMarker + "gate") (actingMarker + "fetch") (readingMarker + "gate")

/// The same wait READING where the recorded run paused.
let private peekPeekPeek: Handler<ToyAction, ToyOp> =
    threeThenAudit "wait-read" (readingMarker + "gate") (readingMarker + "gate") (readingMarker + "gate")

/// Fold-first: merge, then read what the merge left, then the host call.
let private mergeThenRead: Handler<ToyAction, ToyOp> =
    { Name = "fold-first"
      Stages =
        [ Effect(
              ServerEffect.ApplyOps
                  [ Relabel("footer", actingMarker + "merge")
                    Relabel("title", readingMarker + "gate") ]
          )
          Effect(ServerEffect.HostCall("audit", JStr "merged", None)) ] }

/// The acts the toy host performs, each counted: `pause` is the sleep's
/// stand-in, `fetch` a different act, `merge` the fold-first stand-in that
/// WRITES what the read after it reads.
let private actsOf (world: World) (pauses: int ref) (fetches: int ref) (merges: int ref) =
    Map.ofList
        [ "pause",
          fun () ->
              pauses.Value <- pauses.Value + 1
              Ok(JStr "paused")
          "fetch",
          fun () ->
              fetches.Value <- fetches.Value + 1
              Ok(JStr "fetched")
          "merge",
          fun () ->
              merges.Value <- merges.Value + 1
              world.Set("gate", "Merged")
              Ok(JObj []) ]

let private bound (world: World) (pauses: int ref) (plan: PlanRecorders) =
    actingWitness world plan (actsOf world pauses (ref 0) (ref 0))

/// The act routed ROUND the run's actor: it reads through the bound reader and
/// performs its act live — the falsifier for the first case.
let private routedRound (world: World) (pauses: int ref) (plan: PlanRecorders) =
    actingWitness world { plan with Act = PlanActor.live } (actsOf world pauses (ref 0) (ref 0))

let private auditing (audits: int ref) =
    registryOf [ "audit", counting audits "recorded" ]

/// The gate wait killed AFTER its pause, at the second peek's attempt, with
/// the plan built by `witnessOf`. Answers the world, the journal and the
/// pause count the dead run left.
let private waitKilledAfterPause (witnessOf: World -> int ref -> PlanRecorders -> _) =
    let world = World()
    world.Set("gate", "Busy")
    let journal = freshJournal ()
    let pauses = ref 0

    let died =
        crashing (fun () ->
            runPlanning
                (witnessOf world pauses)
                (DurableServices.create
                 |> DurableServices.withJournal (dyingBeforeAttempting 2 journal))
                (auditing (ref 0))
                peekPausePeek)

    Expect.isTrue died "the fixture's process died at the second peek"
    Expect.equal pauses.Value 1 "the pause was performed before the death"
    // The gate moves while the process is down: the resumed second peek, which
    // the dead run never journaled, reads it live.
    world.Set("gate", "Free")
    world, journal, pauses

let private resumed (journal: EffectJournal) (audits: int ref) handler witnessOf =
    runPlanning witnessOf (DurableServices.create |> DurableServices.withJournal journal) (auditing audits) handler

let private planAct =
    testList
        "a plan-phase act (Phase 2222)"
        [ test "killed after the act and resumed, the wait pauses zero more times and plans the same calls" {
              let world, journal, pauses = waitKilledAfterPause bound
              let audits = ref 0
              let outcome = resumed journal audits peekPausePeek (bound world pauses)

              Expect.isTrue outcome.Outcome.Committed "the resumed run committed"
              Expect.equal pauses.Value 1 "the pause was SERVED, not performed again"
              Expect.equal outcome.Replayed [ 0; 1 ] "the first peek and the pause were served"
              Expect.equal outcome.Invoked [ 2; 3 ] "the second peek and the host call ran"
              Expect.equal audits.Value 1 "the host call reached the world once"

              let uninterrupted =
                  let fresh = World()
                  fresh.Set("gate", "Free")
                  resumed (freshJournal ()) (ref 0) peekPausePeek (bound fresh (ref 0))

              Expect.equal
                  outcome.Outcome.Performed
                  uninterrupted.Outcome.Performed
                  "the resumed plan staged the calls an uninterrupted wait stages"

              Expect.equal
                  (labelOf "footer" outcome.Outcome.Store.Tree)
                  (Some "paused")
                  "the plan saw the act's recorded answer"

              Expect.equal
                  (labelOf "title" outcome.Outcome.Store.Tree)
                  (Some "Free")
                  "the second peek, never journaled, read the gate as it is now"

              Expect.equal
                  (journal.Read "inv" |> List.filter (fun e -> e.Step = 1))
                  [ { Invocation = "inv"
                      Step = 1
                      Capability = Durable.PlanActCapability
                      Subject = Some "pause"
                      Phase = JournalPhase.Attempted }
                    { Invocation = "inv"
                      Step = 1
                      Capability = Durable.PlanActCapability
                      Subject = Some "pause"
                      Phase = JournalPhase.Completed(JStr "paused") } ]
                  "journaled as an ACT under PlanAct, the act's name its subject and its answer the value"
          }

          test "GO RED: with the act routed round the run's actor, the same resume pauses a second time" {
              let world, journal, pauses = waitKilledAfterPause routedRound
              let outcome = resumed journal (ref 0) peekPausePeek (routedRound world pauses)

              // Routed round the actor the act takes no ordinal: the dead run
              // journaled peek, peek, and the resume performs the act again.
              Expect.equal pauses.Value 2 "the act ran again: the first case's assertion fails"
              Expect.isTrue outcome.Outcome.Committed "and nothing refused it, which is the hazard"
          }

          test
              "a resume whose plan would perform a DIFFERENT act at that ordinal is refused naming the act, before it is performed" {
              let world, journal, pauses = waitKilledAfterPause bound
              let fetches = ref 0
              let audits = ref 0

              let outcome =
                  resumed journal audits peekFetchPeek (fun plan ->
                      actingWitness world plan (actsOf world pauses fetches (ref 0)))

              Expect.isFalse outcome.Outcome.Committed "refused"

              Expect.equal
                  outcome.Outcome.Diagnostics
                  [ ServerDiagnostic.Failed("ApplyOps", DurableCode.planActDiverged "fetch") ]
                  "the refusal names the act the resumed plan would perform, as an act"

              Expect.equal fetches.Value 0 "the other act was not performed"
              Expect.equal pauses.Value 1 "nor the recorded one again"
              Expect.equal audits.Value 0 "no stage was reached"
          }

          test "a resume whose plan would READ where the record holds an act is refused naming the recorded act" {
              let world, journal, pauses = waitKilledAfterPause bound
              let outcome = resumed journal (ref 0) peekPeekPeek (bound world pauses)

              Expect.equal
                  outcome.Outcome.Diagnostics
                  [ ServerDiagnostic.Failed("ApplyOps", DurableCode.planActDiverged "pause") ]
                  "an act skipped is an act diverged, never a read"
          }

          test "a live (non-durable) placement performs the act every time it plans" {
              let world = World()
              world.Set("gate", "Busy")
              let pauses = ref 0
              let live (_: PlanRecorders) = bound world pauses PlanRecorders.live

              for _ in 1..2 do
                  let outcome = resumed (freshJournal ()) (ref 0) peekPausePeek live
                  Expect.isTrue outcome.Outcome.Committed "each run committed"

              Expect.equal pauses.Value 2 "two plans, two pauses: nothing journaled, nothing served"

              let journal = freshJournal ()

              let died =
                  crashing (fun () ->
                      runPlanning
                          live
                          (DurableServices.create
                           |> DurableServices.withJournal (dyingBeforeAttempting 0 journal))
                          (auditing (ref 0))
                          peekPausePeek)

              Expect.isTrue died "killed at the host call"
              resumed journal (ref 0) peekPausePeek live |> ignore
              Expect.equal pauses.Value 4 "and a resumed live plan pauses again"
          }

          test
              "an act that WRITES, killed after the act and resumed, is performed zero more times and the read after it sees what it left" {
              let world = World()
              let merges = ref 0
              let journal = freshJournal ()
              let audits = ref 0

              let witnessOf plan =
                  actingWitness world plan (actsOf world (ref 0) (ref 0) merges)

              let died =
                  crashing (fun () ->
                      runPlanning
                          witnessOf
                          (DurableServices.create
                           |> DurableServices.withJournal (dyingBeforeAttempting 1 journal))
                          (auditing audits)
                          mergeThenRead)

              Expect.isTrue died "the process died after the merge, at the read's attempt"
              Expect.equal merges.Value 1 "the merge was performed"

              let outcome = resumed journal audits mergeThenRead witnessOf

              Expect.isTrue outcome.Outcome.Committed "the resumed run committed"
              Expect.equal merges.Value 1 "the merge was served, not performed again"
              Expect.equal outcome.Replayed [ 0 ] "the act was served"
              Expect.equal outcome.Invoked [ 1; 2 ] "the read and the host call ran"

              Expect.equal
                  (labelOf "title" outcome.Outcome.Store.Tree)
                  (Some "Merged")
                  "the entry read after the act read the value the act left"

              Expect.equal audits.Value 1 "the host call reached the world once"
          }

          test
              "a process that died INSIDE an act is refused as indeterminate, unless the host declared that act safe to repeat" {
              let world = World()
              world.Set("gate", "Busy")
              let pauses = ref 0
              let journal = freshJournal ()

              let dyingPause () =
                  pauses.Value <- pauses.Value + 1

                  if pauses.Value = 1 then
                      raise (ProcessDied "inside the pause")

                  Ok(JStr "paused")

              let witnessOf plan =
                  actingWitness world plan (Map.ofList [ "pause", dyingPause ])

              let died = crashing (fun () -> resumed journal (ref 0) peekPausePeek witnessOf)

              Expect.isTrue died "the process died inside the pause"

              let refused = resumed journal (ref 0) peekPausePeek witnessOf

              Expect.equal
                  refused.Outcome.Diagnostics
                  [ ServerDiagnostic.Failed("ApplyOps", DurableCode.IndeterminateStep) ]
                  "an undeclared act is NonIdempotent: the window is refused"

              Expect.equal pauses.Value 1 "and not performed again"

              let declared =
                  runPlanning
                      witnessOf
                      (DurableServices.create
                       |> DurableServices.withJournal journal
                       |> DurableServices.declaringPlanAct "pause" IdempotencyFacet.Idempotent)
                      (auditing (ref 0))
                      peekPausePeek

              Expect.isTrue declared.Outcome.Committed "a declared-idempotent act closes its window by acting again"
              Expect.equal pauses.Value 2 "performed once more"
              Expect.isEmpty declared.Overrides "with no override to record"
          } ]

// ─── F-RECEIPTS ──────────────────────────────────────────────────────────────

let private twoEdits: Handler<ToyAction, ToyOp> =
    { Name = "two-edits"
      Stages = [ Effect(ServerEffect.ApplyOps [ Relabel("title", "One"); Relabel("footer", "Two") ]) ] }

/// A performer that records the prefix it was handed per op and answers the
/// label it landed.
let private recordingPrefix (seen: System.Collections.Generic.List<string * string option * OpReceipt list>) =
    OpPerformance.performedWithPrefix (fun prefix state op ->
        match op with
        | Relabel(id, label) ->
            seen.Add(id, labelOf id prefix.Before, prefix.Receipts)
            Ok(OpReceipt.ofDetail (JStr label)))

let private prefix =
    testList
        "the run's prefix at the performer and the contract (F-RECEIPTS)"
        [ test
              "each op stage is handed the state it was applied TO and the receipts of the stages before it, in perform order" {
              let seen = System.Collections.Generic.List<_>()

              let outcome =
                  Handler.runWith
                      witness
                      (registryOf [])
                      (recordingPrefix seen)
                      Fuaran.Compute.DataFrame.noResolve
                      "node"
                      twoEdits
                      emptyStore

              Expect.isTrue outcome.Committed "committed"

              Expect.equal
                  (List.ofSeq seen)
                  [ "title", Some "Draft", []
                    "footer", Some "Plain", [ OpReceipt.ofDetail (JStr "One") ] ]
                  "the first op saw the entry state and no receipts; the second saw the first's receipt"
          }

          test "a contract can state what an op OWED and be checked: the first op owed nothing, the second one receipt" {
              let owed (n: int) : OpContract<ToyNode, ToyOp> =
                  { Name = sprintf "owed-%d" n
                    Holds = fun prefix _ _ _ -> List.length prefix.Receipts = n }

              let honest =
                  Handler.runWith
                      witness
                      (registryOf [])
                      (OpPerformance.performedChecked
                          [ { Name = "owed-its-position"
                              Holds =
                                fun prefix _ op _ ->
                                    match op with
                                    | Relabel("title", _) -> prefix.Receipts = []
                                    | Relabel _ -> prefix.Receipts = [ OpReceipt.ofDetail (JStr "One") ] } ]
                          (fun _ _ op ->
                              match op with
                              | Relabel(_, label) -> Ok(OpReceipt.ofDetail (JStr label))))
                      Fuaran.Compute.DataFrame.noResolve
                      "node"
                      twoEdits
                      emptyStore

              Expect.isTrue honest.Committed "a contract over the prefix holds where the prefix is what it says"

              let lying =
                  Handler.runWith
                      witness
                      (registryOf [])
                      (OpPerformance.performedChecked [ owed 2 ] (fun _ _ op ->
                          match op with
                          | Relabel(_, label) -> Ok(OpReceipt.ofDetail (JStr label))))
                      Fuaran.Compute.DataFrame.noResolve
                      "node"
                      twoEdits
                      emptyStore

              Expect.isFalse lying.Committed "refused"

              Expect.equal
                  lying.Diagnostics
                  [ ServerDiagnostic.PerformFailed("ApplyOps", "return-contract:owed-2") ]
                  "the contract that refused, named, at the first op"

              Expect.equal lying.Performed [] "nothing was reported performed"
          }

          test "on a resume the served stage's RECORDED receipt is in the prefix the next performer is handed" {
              let journal = freshJournal ()
              let seen = System.Collections.Generic.List<_>()

              let died =
                  crashing (fun () ->
                      Durable.runWith
                          witness
                          (DurableServices.create
                           |> DurableServices.withJournal (dyingBeforeAttempting 1 journal))
                          "inv"
                          (registryOf [])
                          (recordingPrefix seen)
                          Fuaran.Compute.DataFrame.noResolve
                          "node"
                          twoEdits
                          emptyStore)

              Expect.isTrue died "died between the two op stages"
              Expect.equal (List.ofSeq seen |> List.map (fun (id, _, _) -> id)) [ "title" ] "the first op performed"
              seen.Clear()

              let resumed =
                  Durable.runWith
                      witness
                      (DurableServices.create |> DurableServices.withJournal journal)
                      "inv"
                      (registryOf [])
                      (recordingPrefix seen)
                      Fuaran.Compute.DataFrame.noResolve
                      "node"
                      twoEdits
                      emptyStore

              Expect.isTrue resumed.Outcome.Committed "committed"
              Expect.equal resumed.Replayed [ 0 ] "the first op was served"

              Expect.equal
                  (List.ofSeq seen)
                  [ "footer", Some "Plain", [ OpReceipt.ofDetail (JStr "One") ] ]
                  "the second op's performer was handed the served receipt as its prefix"
          } ]

// ─── F-FACET ─────────────────────────────────────────────────────────────────

/// The toy witness with a reach that names an effect KIND per op: the title's
/// relabel is a `write`, the footer's a `push`.
let private kindedWitness =
    { witness with
        State =
            { witness.State with
                Reach =
                    fun op ->
                        match op with
                        | Relabel(id, _) ->
                            { Arguments = [ (if id = "title" then "write" else "push"), id ]
                              Destination = EffectDestination.Absent } } }

/// An op performer that performs the relabel of `victim` and then dies — the
/// crash inside the indeterminate window.
let private dyingInside (victim: string) (performed: int ref) : OpPerformance<ToyNode, ToyOp> =
    OpPerformance.performedWithoutReceipt (fun _ op ->
        performed.Value <- performed.Value + 1

        match op with
        | Relabel(id, _) when id = victim -> raise (ProcessDied "inside the op")
        | _ -> Ok())

let private oneEdit (id: string) : Handler<ToyAction, ToyOp> =
    { Name = "edit-" + id
      Stages = [ Effect(ServerEffect.ApplyOps [ Relabel(id, "Edited") ]) ] }

let private perKind =
    DurableServices.create
    |> DurableServices.declaringOpKind "write" IdempotencyFacet.Idempotent
    |> DurableServices.declaringOpKind "push" IdempotencyFacet.NonIdempotent

let private crashInside (id: string) =
    let journal = freshJournal ()
    let performed = ref 0

    let died =
        crashing (fun () ->
            Durable.runWith
                kindedWitness
                (perKind |> DurableServices.withJournal journal)
                "inv"
                (registryOf [])
                (dyingInside id performed)
                Fuaran.Compute.DataFrame.noResolve
                "node"
                (oneEdit id)
                emptyStore)

    Expect.isTrue died "the fixture died inside the op"
    Expect.equal performed.Value 1 "the op was attempted once"
    journal

let private facet =
    testList
        "an idempotency facet per effect kind (F-FACET)"
        [ test
              "the facet of an op is the meet over the kinds its reach names; an undeclared kind reads as the whole-performer declaration" {
              let facets = perKind.Performers

              Expect.equal (PerformerFacets.opFacetOf [ "write" ] facets) IdempotencyFacet.Idempotent "a write"
              Expect.equal (PerformerFacets.opFacetOf [ "push" ] facets) IdempotencyFacet.NonIdempotent "a push"

              Expect.equal
                  (PerformerFacets.opFacetOf [ "write"; "push" ] facets)
                  IdempotencyFacet.NonIdempotent
                  "an op that both writes and pushes repeats as a push does"

              Expect.equal
                  (PerformerFacets.opFacetOf [ "commit" ] facets)
                  IdempotencyFacet.NonIdempotent
                  "a kind nobody declared, with no whole-performer declaration, is non-idempotent"

              Expect.equal
                  (PerformerFacets.opFacetOf
                      [ "commit" ]
                      (PerformerFacets.declareOpPerformer IdempotencyFacet.IdempotentWithStore facets))
                  IdempotencyFacet.IdempotentWithStore
                  "a kind nobody declared reads as the whole-performer declaration where one was made"

              Expect.equal
                  (PerformerFacets.opFacetOf [] facets)
                  IdempotencyFacet.NonIdempotent
                  "an op naming no kind reads as the whole-performer declaration"

              Expect.equal
                  (PerformerFacets.opPerformerFacet facets)
                  IdempotencyFacet.NonIdempotent
                  "the arm as a whole, with a push declared, is non-idempotent: the static reading is the meet"

              Expect.equal
                  (PerformerFacets.opPerformerFacet (
                      PerformerFacets.none
                      |> PerformerFacets.declareOpKind "write" IdempotencyFacet.Idempotent
                  ))
                  IdempotencyFacet.Idempotent
                  "an arm whose every declared kind is idempotent is idempotent"

              Expect.isTrue (PerformerFacets.isOpPerformerDeclared facets) "declaring a kind declares the performer"

              Expect.equal
                  (Durable.opKinds kindedWitness.State (Relabel("title", "x")))
                  [ "write" ]
                  "the kinds of an op are the argument names its reach declares"

              Expect.equal
                  (Durable.opKinds witness.State (Relabel("title", "x")))
                  [ "target" ]
                  "and at the plain toy witness, its one reach argument"
          }

          test
              "a crash inside a WRITE closes its window by re-invoking: the kind is declared idempotent, no override is recorded" {
              let journal = crashInside "title"
              let performed = ref 0

              let resumed =
                  Durable.runWith
                      kindedWitness
                      (perKind |> DurableServices.withJournal journal)
                      "inv"
                      (registryOf [])
                      (OpPerformance.performedWithoutReceipt (fun _ _ ->
                          performed.Value <- performed.Value + 1
                          Ok()))
                      Fuaran.Compute.DataFrame.noResolve
                      "node"
                      (oneEdit "title")
                      emptyStore

              Expect.isTrue resumed.Outcome.Committed "committed"
              Expect.equal resumed.Invoked [ 0 ] "re-invoked"
              Expect.isEmpty resumed.Overrides "no override: the kind's own shape closed the window"
              Expect.isEmpty resumed.Indeterminate "nothing undecided"
              Expect.equal performed.Value 1 "performed once on the resume"
          }

          test "a crash inside a PUSH is refused as indeterminate under the same declaration" {
              let journal = crashInside "footer"
              let performed = ref 0

              let resumed =
                  Durable.runWith
                      kindedWitness
                      (perKind |> DurableServices.withJournal journal)
                      "inv"
                      (registryOf [])
                      (OpPerformance.performedWithoutReceipt (fun _ _ ->
                          performed.Value <- performed.Value + 1
                          Ok()))
                      Fuaran.Compute.DataFrame.noResolve
                      "node"
                      (oneEdit "footer")
                      emptyStore

              Expect.isFalse resumed.Outcome.Committed "refused"
              Expect.equal resumed.Indeterminate [ 0 ] "the push's ordinal is undecided"
              Expect.equal performed.Value 0 "not re-invoked"

              Expect.equal
                  resumed.Outcome.Diagnostics
                  [ ServerDiagnostic.PerformFailed("ApplyOps", DurableCode.IndeterminateStep) ]
                  "under durable-indeterminate-step"
          } ]

// ─── F-CONTRACTS ─────────────────────────────────────────────────────────────

let private contracts =
    testList
        "contracts composed by Program (F-CONTRACTS)"
        [ test "a list of contracts is checked in order, and the FIRST that rejects names the refusal" {
              let named (name: string) (holds: bool) : OpContract<ToyNode, ToyOp> =
                  OpContract.at name (fun _ _ _ -> holds)

              let under (contracts: OpContract<ToyNode, ToyOp> list) =
                  Handler.runWith
                      witness
                      (registryOf [])
                      (OpPerformance.performedChecked contracts (fun _ _ _ -> Ok(OpReceipt.ofDetail (JStr "receipt"))))
                      Fuaran.Compute.DataFrame.noResolve
                      "node"
                      (oneEdit "title")
                      emptyStore

              let refusal (outcome: HandlerOutcome<ToyNode, ToyStore, ToyOp, ToyEffect>) =
                  outcome.Diagnostics
                  |> List.tryPick (fun d ->
                      match d with
                      | ServerDiagnostic.PerformFailed("ApplyOps", reason) -> Some reason
                      | _ -> None)

              Expect.isTrue (under []).Committed "no contract: the performer unchecked"
              Expect.isTrue (under [ named "a" true; named "b" true ]).Committed "every contract holds"

              Expect.equal
                  (refusal (under [ named "a" false; named "b" false ]))
                  (Some "return-contract:a")
                  "the first in declaration order names the refusal"

              Expect.equal
                  (refusal (under [ named "b" false; named "a" false ]))
                  (Some "return-contract:b")
                  "and the order is the host's"

              Expect.equal
                  (refusal (under [ named "a" true; named "b" false ]))
                  (Some "return-contract:b")
                  "a holding contract is passed through to the next"
          }

          test "checkAll is the nesting of check, so a host that composed by hand reads the same refusal" {
              let a = OpContract.at "a" (fun _ _ _ -> false)
              let b = OpContract.at "b" (fun _ _ _ -> false)
              let perform (_: OpPrefix<ToyNode>) (_: ToyNode) (_: ToyOp) = Ok(OpReceipt.ofDetail (JStr "receipt"))
              let prefix = OpPrefix.atEntry baseTree

              Expect.equal
                  (OpContract.checkAll [ a; b ] perform prefix baseTree (Relabel("title", "x")))
                  (OpContract.check b (OpContract.check a perform) prefix baseTree (Relabel("title", "x")))
                  "the list is the nesting, the first declared innermost — so it is asked first"

              Expect.equal
                  (OpContract.checkAll [] perform prefix baseTree (Relabel("title", "x")))
                  (Ok(OpReceipt.ofDetail (JStr "receipt")))
                  "the empty list is the performer"
          } ]

// ─── the model beside production ─────────────────────────────────────────────

/// The journal snapshot as the model reads it, from the production journal's
/// own entries — `ToyDurableReplayTests`'s adaptor, restated for the read.
let private modelJournal (entries: JournalEntry list) : Staging.journal<JVal> =
    { j_step =
        fun k ->
            match Journal.stepOf entries (int k) with
            | JournaledStep.Unrun -> Staging.JUnrun
            | JournaledStep.Value v -> Staging.JValue v
            | JournaledStep.Refusal r -> Staging.JRefusal r
            | JournaledStep.Indeterminate _ -> Staging.JIndeterminate
      j_recorded =
        fun k ->
            match Journal.capabilityOf entries (int k), Journal.subjectOf entries (int k) with
            | Some capability, Some subject ->
                Staging.OSome(
                    capability,
                    (match subject with
                     | Some s -> Staging.OSome s
                     | None -> Staging.ONone)
                )
            | _ -> Staging.ONone }

let private entry (step: int) (capability: string) (subject: string option) (phase: JournalPhase) : JournalEntry =
    { Invocation = "inv"
      Step = step
      Capability = capability
      Subject = subject
      Phase = phase }

/// What production's reader answered the plan, observed through the
/// witness: the read's answer is what `Apply` relabels with, or the refusal
/// the plan halts on.
let private productionRead (entries: JournalEntry list) (live: string) : Result<JVal, string> =
    let journal = freshJournal ()
    entries |> List.iter journal.Append
    let world = World()
    world.Set("bundle", live)
    let answered = ref None

    let observing (reader: EntryReader) =
        readingWitness world (fun subject read ->
            let r = reader subject read
            answered.Value <- Some r
            r)

    run
        (observing)
        (DurableServices.create |> DurableServices.withJournal journal)
        "inv"
        (registryOf [ "audit", fun _ -> Ok(JStr "recorded") ])
        (OpPerformance.performedWithoutReceipt (fun _ _ -> Ok()))
        readThenRetireThenAudit
    |> ignore

    answered.Value |> Option.defaultWith (fun () -> failtest "the plan never read")

let private modelRead (entries: JournalEntry list) (live: string) : Result<JVal, string> =
    match Staging.entry_read (modelJournal entries) (bigint 0) "bundle" (Staging.ROk(JStr live)) with
    | Staging.ROk v -> Ok v
    | Staging.RErr r -> Error r

let private readShapes: (string * JournalEntry list) list =
    [ "nothing recorded", []
      "the read completed",
      [ entry 0 Durable.EntryReadCapability (Some "bundle") JournalPhase.Attempted
        entry 0 Durable.EntryReadCapability (Some "bundle") (JournalPhase.Completed(JStr "Recorded")) ]
      "the read refused",
      [ entry 0 Durable.EntryReadCapability (Some "bundle") JournalPhase.Attempted
        entry 0 Durable.EntryReadCapability (Some "bundle") (JournalPhase.Refused "the host could not read") ]
      "the read attempted and undecided", [ entry 0 Durable.EntryReadCapability (Some "bundle") JournalPhase.Attempted ]
      "another read recorded at the ordinal",
      [ entry 0 Durable.EntryReadCapability (Some "other") JournalPhase.Attempted
        entry 0 Durable.EntryReadCapability (Some "other") (JournalPhase.Completed(JStr "Recorded")) ]
      "an op stage recorded at the ordinal",
      [ entry 0 Durable.OpStageCapability (Some "sha256:0") JournalPhase.Attempted
        entry 0 Durable.OpStageCapability (Some "sha256:0") (JournalPhase.Completed(JObj [])) ] ]

let private oracle =
    testList
        "the proved entry read as oracle"
        [ for label, entries in readShapes do
              test (sprintf "%s: the extracted entry_read and production's reader agree" label) {
                  Expect.equal (productionRead entries "Live") (modelRead entries "Live") label
              }
          test "GO RED: a model fed another subject disagrees with production, so the comparison can lose" {
              let entries = snd readShapes[1]

              let model =
                  match Staging.entry_read (modelJournal entries) (bigint 0) "other" (Staging.ROk(JStr "Live")) with
                  | Staging.ROk v -> Ok v
                  | Staging.RErr r -> Error r

              Expect.notEqual (productionRead entries "Live") model "the model refuses the read production serves"
          } ]

[<Tests>]
let tests =
    testList
        "Phase 2165 - the durable tier at the toy witness: the entry read, the prefix, per-kind facets and composed contracts"
        [ entryRead; planAct; prefix; facet; contracts; oracle ]
