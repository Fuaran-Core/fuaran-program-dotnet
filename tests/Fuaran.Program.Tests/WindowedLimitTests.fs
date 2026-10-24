/// Phase 2260 (D52) — effects are limited over TIME by the host, at the toy
/// witness: a count per window, a cumulative quantity per window and a minimum
/// dwell, declared as policy clauses, decided at the gate's own position from
/// a clock the host supplies and counters the store holds under the reserved
/// prefix, journaled decision by decision, and reproduced on replay from the
/// journal alone.
module Fuaran.Program.Tests.WindowedLimitTests

open Expecto
open Fuaran.Core
open Fuaran.Program.Bounded
open Fuaran.Program.Server
open Fuaran.Program.Tests.ToyDomain

// ─── fixtures ────────────────────────────────────────────────────────────────

exception private ProcessDied of string

let private leaf id label =
    { Id = id
      Label = Const(JStr label)
      Handlers = []
      Children = [] }

let private emptyStore: ServerStore<ToyNode, ToyStore> =
    { Tree =
        { Id = "root"
          Label = Const(JStr "root")
          Handlers = []
          Children = [ leaf "title" "Draft" ] }
      Bindings = Map.empty }

/// The one capability every case limits.
let private Audit = "host:audit"

/// The counters' key under the toy's reserved prefix (`sys.`).
let private CounterKey = WindowCounter.key ReservedPrefix Audit

/// A host clock the test turns by hand: the reading the run takes is whatever
/// `now` holds when the run reaches its first windowed decision.
type private Clock() =
    member val Now = 0L with get, set

    member this.Services(journal: EffectJournal) : DurableServices =
        DurableServices.create
        |> DurableServices.withJournal journal
        |> DurableServices.withClock (fun () -> this.Now)

/// A registry that admits `audit`, counts its invocations, and bounds it by
/// the clauses under test.
let private registryOf (performed: int ref) (clauses: ServerConstraintClause list) : ServerEffectRegistry =
    ServerEffectRegistry.denyAll
    |> ServerEffectRegistry.register "audit" (fun _ ->
        performed.Value <- performed.Value + 1
        Ok(JStr "audited"))
    |> ServerEffectRegistry.permissive
    |> ServerEffectRegistry.constrain Audit clauses

/// One host call with the given arguments.
let private calling (args: (string * JVal) list) : Handler<ToyAction, ToyOp> =
    { Name = "audit"
      Stages = [ Effect(ServerEffect.HostCall("audit", JObj args, None)) ] }

let private audit = calling []

let private run
    (services: DurableServices)
    (invocation: string)
    (registry: ServerEffectRegistry)
    (handler: Handler<ToyAction, ToyOp>)
    (store: ServerStore<ToyNode, ToyStore>)
    =
    Durable.runWith
        witness
        services
        invocation
        registry
        OpPerformance.InMemory
        Fuaran.Compute.DataFrame.noResolve
        "node"
        handler
        store

/// The halt reason the policy refused with, if the run halted on one.
let private refusal (outcome: DurableOutcome<ToyNode, ToyStore, ToyOp, ToyEffect>) : string option =
    outcome.Outcome.Diagnostics
    |> List.tryPick (fun d ->
        match d with
        | ServerDiagnostic.Failed(capability, reason) when capability = Audit -> Some reason
        | _ -> None)

let private counterIn (store: ServerStore<ToyNode, ToyStore>) : WindowCounter option =
    Map.tryFind CounterKey store.Bindings
    |> Option.map (fun held ->
        match WindowCounter.decode held with
        | Ok counter -> counter
        | Error reason -> failtestf "the stored counter does not decode: %s" reason)

/// Run a sequence of invocations at the given instants, each against the
/// store the previous one left, answering what each decided.
let private sequence
    (clock: Clock)
    (services: DurableServices)
    (registry: ServerEffectRegistry)
    (handler: Handler<ToyAction, ToyOp>)
    (instants: int64 list)
    =
    instants
    |> List.mapi (fun i at -> i, at)
    |> List.fold
        (fun (store, decided) (i, at) ->
            clock.Now <- at
            let outcome = run services $"i{i}" registry handler store
            outcome.Outcome.Store, decided @ [ outcome ])
        (emptyStore, [])

let private committedOf (outcomes: DurableOutcome<ToyNode, ToyStore, ToyOp, ToyEffect> list) =
    outcomes |> List.map (fun o -> o.Outcome.Committed)

// ─── the three limits ────────────────────────────────────────────────────────

let private limits =
    testList
        "the three declared limits"
        [ test
              "N per window refuses the N+1th inside the window and admits after it, and the counter lives under the reserved prefix" {
              let performed = ref 0
              let clock = Clock()
              let registry = registryOf performed [ ServerConstraintClause.PerWindow(2, 1000) ]

              let store, outcomes =
                  sequence clock (clock.Services(Journal.inMemory ())) registry audit [ 0L; 10L; 20L; 999L; 1000L ]

              Expect.equal
                  (committedOf outcomes)
                  [ true; true; false; false; true ]
                  "two admitted, the third and fourth refused inside the window, the fifth admitted after it"

              Expect.equal performed.Value 3 "the performer ran exactly for the admissions"

              Expect.equal
                  (refusal outcomes[2])
                  (Some "admissions-over-window:2/1000")
                  "the refusal names the declaration — the count and the window — and never the reading"

              Expect.isTrue (CounterKey.StartsWith ReservedPrefix) "the counters live under the host-reserved prefix"

              match counterIn store with
              | Some counter ->
                  Expect.equal counter.Count 1 "the fifth admission opened a fresh window"
                  Expect.equal counter.Since 1000L "anchored at the admission that opened it"
                  Expect.equal counter.Last (Some 1000L) "the last admission"
              | None -> failtest "the counters were not written back"
          }

          test
              "a cumulative quantity cap sums the named argument over the window, refuses what would exceed it and admits what fits" {
              let performed = ref 0
              let clock = Clock()

              let registry =
                  registryOf performed [ ServerConstraintClause.QuantityPerWindow("amount", 100, 1000) ]

              let services = clock.Services(Journal.inMemory ())
              let first = run services "i0" registry (calling [ "amount", JInt 60 ]) emptyStore
              clock.Now <- 10L

              let second =
                  run services "i1" registry (calling [ "amount", JInt 50 ]) first.Outcome.Store

              clock.Now <- 20L

              let third =
                  run services "i2" registry (calling [ "amount", JInt 40 ]) second.Outcome.Store

              clock.Now <- 1000L

              let fourth =
                  run services "i3" registry (calling [ "amount", JInt 100 ]) third.Outcome.Store

              Expect.equal
                  (committedOf [ first; second; third; fourth ])
                  [ true; false; true; true ]
                  "60 admitted, 50 would exceed 100 and is refused, 40 fits, and after the window 100 fits again"

              Expect.equal
                  (refusal second)
                  (Some "quantity-over-window:amount:100/1000")
                  "the refusal names the argument, the cap and the window, never the value"

              Expect.equal performed.Value 3 "the performer ran for the admissions alone"

              match counterIn third.Outcome.Store with
              | Some counter -> Expect.equal counter.Quantity 100L "the sum inside the window"
              | None -> failtest "no counter"
          }

          test
              "a negative or non-integer quantity is refused under the argument's name — a negative contribution would buy back a spent cap" {
              let performed = ref 0
              let clock = Clock()

              let registry =
                  registryOf performed [ ServerConstraintClause.QuantityPerWindow("amount", 100, 1000) ]

              let services = clock.Services(Journal.inMemory ())
              let negative = run services "i0" registry (calling [ "amount", JInt -5 ]) emptyStore
              let text = run services "i1" registry (calling [ "amount", JStr "lots" ]) emptyStore
              Expect.equal (refusal negative) (Some "argument-not-allowed:amount") "a negative quantity"
              Expect.equal (refusal text) (Some "argument-not-allowed:amount") "a value that is not an integer"
              Expect.equal performed.Value 0 "nothing ran"
              Expect.isNone (counterIn negative.Outcome.Store) "a refusal is not an admission: no counter was written"
          }

          test "a minimum dwell refuses an admission inside it and admits one at it" {
              let performed = ref 0
              let clock = Clock()
              let registry = registryOf performed [ ServerConstraintClause.Dwell 500 ]

              let _, outcomes =
                  sequence clock (clock.Services(Journal.inMemory ())) registry audit [ 0L; 300L; 499L; 500L; 999L ]

              Expect.equal
                  (committedOf outcomes)
                  [ true; false; false; true; false ]
                  "admitted, inside the dwell twice, admitted at it, inside again"

              Expect.equal (refusal outcomes[1]) (Some "within-dwell:500") "the refusal names the dwell"
              Expect.equal performed.Value 2 "two admissions"
          }

          test "the three compose: the dwell is decided first, then the count, then the quantity" {
              let performed = ref 0
              let clock = Clock()

              let registry =
                  registryOf
                      performed
                      [ ServerConstraintClause.PerWindow(1, 1000)
                        ServerConstraintClause.QuantityPerWindow("amount", 10, 1000)
                        ServerConstraintClause.Dwell 100 ]

              let services = clock.Services(Journal.inMemory ())
              let first = run services "i0" registry (calling [ "amount", JInt 5 ]) emptyStore
              clock.Now <- 50L

              let second =
                  run services "i1" registry (calling [ "amount", JInt 5 ]) first.Outcome.Store

              clock.Now <- 100L

              let third =
                  run services "i2" registry (calling [ "amount", JInt 5 ]) second.Outcome.Store

              Expect.isTrue first.Outcome.Committed "the first is admitted by all three"
              Expect.equal (refusal second) (Some "within-dwell:100") "inside the dwell, the dwell names the refusal"

              Expect.equal
                  (refusal third)
                  (Some "admissions-over-window:1/1000")
                  "past the dwell, the count names it — the quantity would have fitted"
          }

          test "a stateless clause that refuses first means nothing was admitted and nothing is counted" {
              let performed = ref 0
              let clock = Clock()

              let registry =
                  registryOf
                      performed
                      [ ServerConstraintClause.AllowList("target", [ "a" ])
                        ServerConstraintClause.PerWindow(1, 1000) ]

              let services = clock.Services(Journal.inMemory ())
              let refused = run services "i0" registry (calling [ "target", JStr "b" ]) emptyStore
              Expect.equal (refusal refused) (Some "argument-not-allowed:target") "the allow-list refused"
              Expect.isNone (counterIn refused.Outcome.Store) "no admission, no counter"

              let admitted =
                  run services "i1" registry (calling [ "target", JStr "a" ]) refused.Outcome.Store

              Expect.isTrue admitted.Outcome.Committed "the window was not spent by the refusal"
          }

          test
              "a windowed clause nobody can judge is refused, never admitted: no clock, no store channel, a non-positive window" {
              let performed = ref 0
              let registry = registryOf performed [ ServerConstraintClause.PerWindow(2, 1000) ]

              let unclocked =
                  run
                      (DurableServices.create |> DurableServices.withJournal (Journal.inMemory ()))
                      "i0"
                      registry
                      audit
                      emptyStore

              Expect.equal
                  (refusal unclocked)
                  (Some "limit-unjudgeable:no-clock")
                  "the durable interpreter without a clock"

              let direct =
                  Handler.runWith
                      witness
                      registry
                      OpPerformance.InMemory
                      Fuaran.Compute.DataFrame.noResolve
                      "node"
                      audit
                      emptyStore

              Expect.equal
                  (direct.Diagnostics
                   |> List.tryPick (fun d ->
                       match d with
                       | ServerDiagnostic.Failed(_, reason) -> Some reason
                       | _ -> None))
                  (Some "limit-unjudgeable:no-clock")
                  "the direct interpreter has no clock at all"

              let clock = Clock()

              let zero =
                  run
                      (clock.Services(Journal.inMemory ()))
                      "i1"
                      (registryOf performed [ ServerConstraintClause.Dwell 0 ])
                      audit
                      emptyStore

              Expect.equal (refusal zero) (Some "limit-unjudgeable:window-not-positive") "a dwell of zero"
              Expect.equal performed.Value 0 "nothing ran"
          } ]

// ─── the journal: the clock read, the decisions, and replay ─────────────────

/// A journal the process dies in front of: the ATTEMPT record for `step`
/// kills the process before it lands.
let private dyingBeforeAttempting (step: int) (inner: EffectJournal) : EffectJournal =
    { inner with
        Append =
            fun entry ->
                match entry.Phase with
                | JournalPhase.Attempted when entry.Step = step -> raise (ProcessDied "between steps")
                | _ -> inner.Append entry }

let private journal =
    testList
        "the journal"
        [ test
              "the clock is read once per invocation and every decision is journaled at its ordinal — admissions and refusals both" {
              let performed = ref 0
              let clock = Clock()
              let journal = Journal.inMemory ()
              let registry = registryOf performed [ ServerConstraintClause.PerWindow(1, 1000) ]

              let two =
                  { Name = "twice"
                    Stages =
                      [ Effect(ServerEffect.HostCall("audit", JObj [], None))
                        Effect(ServerEffect.HostCall("audit", JObj [], None)) ] }

              let outcome = run (clock.Services journal) "i0" registry two emptyStore
              Expect.isFalse outcome.Outcome.Committed "the second call breached the window"

              Expect.equal
                  (Journal.describe (journal.Read "i0"))
                  [ "0 ReadClock attempted"
                    "0 ReadClock completed"
                    "1 Limit host:audit attempted"
                    "1 Limit host:audit completed"
                    "2 Limit host:audit attempted"
                    "2 Limit host:audit refused"
                    "-1 Invocation completed" ]
                  "one clock read, then one record per decision: the admission completed, the refusal refused"

              Expect.equal performed.Value 0 "the plan halted before the perform phase"
          }

          test
              "a run that dies mid-window resumes against the journal: the clock and the decision are SERVED, the live clock is not consulted, and the admission is performed once" {
              let performed = ref 0
              let clock = Clock()
              let inner = Journal.inMemory ()
              let registry = registryOf performed [ ServerConstraintClause.PerWindow(1, 1000) ]

              // Ordinals: 0 the clock read, 1 the decision, 2 the host call.
              let died =
                  try
                      run (clock.Services(dyingBeforeAttempting 2 inner)) "i0" registry audit emptyStore
                      |> ignore

                      false
                  with ProcessDied _ ->
                      true

              Expect.isTrue died "the process died at the host call's attempt"
              Expect.equal performed.Value 0 "nothing performed before the death"

              // The clock has moved past the window; a run that re-read it would
              // decide differently. The resume is served the recorded reading.
              clock.Now <- 5000L
              let resumed = run (clock.Services inner) "i0" registry audit emptyStore
              Expect.isTrue resumed.Outcome.Committed "the resume completed the run"
              Expect.equal resumed.Replayed [ 0; 1 ] "the clock read and the decision were served"
              Expect.equal resumed.Invoked [ 2 ] "the host call was performed"
              Expect.equal performed.Value 1 "once"

              match counterIn resumed.Outcome.Store with
              | Some counter ->
                  Expect.equal
                      counter.Since
                      0L
                      "the counter is the dead run's decision, anchored at the recorded reading"
              | None -> failtest "no counter"
          }

          test
              "replay reproduces every decision from the journal: a completed invocation re-run invokes nothing and reaches the same store, and a refused one is refused again" {
              let performed = ref 0
              let clock = Clock()
              let journal = Journal.inMemory ()
              let registry = registryOf performed [ ServerConstraintClause.PerWindow(1, 1000) ]

              let first = run (clock.Services journal) "i0" registry audit emptyStore
              clock.Now <- 10L
              let second = run (clock.Services journal) "i1" registry audit first.Outcome.Store
              Expect.isTrue first.Outcome.Committed "admitted"
              Expect.isFalse second.Outcome.Committed "refused inside the window"

              clock.Now <- 99_999L
              let firstAgain = run (clock.Services journal) "i0" registry audit emptyStore

              let secondAgain =
                  run (clock.Services journal) "i1" registry audit first.Outcome.Store

              Expect.equal firstAgain.Invoked [] "nothing invoked on replay"
              Expect.equal firstAgain.Replayed [ 0; 1; 2 ] "every ordinal served"

              Expect.equal
                  firstAgain.Outcome.Store.Bindings
                  first.Outcome.Store.Bindings
                  "the same store, counters included"

              Expect.equal secondAgain.Outcome.Committed false "the refusal is reproduced"
              Expect.equal (refusal secondAgain) (refusal second) "with the recorded token"
              Expect.equal performed.Value 1 "the performer ran once across four runs"
          } ]

// ─── the demanded document ───────────────────────────────────────────────────

let private demanded =
    testList
        "the demanded document"
        [ test "the three clauses ride the document at version 12 and read back clause for clause" {
              let performed = ref 0

              let registry =
                  registryOf
                      performed
                      [ ServerConstraintClause.PerWindow(2, 1000)
                        ServerConstraintClause.QuantityPerWindow("amount", 100, 60_000)
                        ServerConstraintClause.Dwell 500 ]

              let projection =
                  ServerDemanded.ofHandler witness audit
                  |> ServerDemanded.withConstraints registry

              let document = Demanded.encode projection
              Expect.equal Demanded.Version 12 "the version the clauses widened"
              Expect.stringContains document "\"version\":12" "carried in the document"

              Expect.stringContains
                  document
                  "{\"clause\":\"perWindow\",\"count\":2,\"window\":1000}"
                  "the count per window"

              Expect.stringContains
                  document
                  "{\"clause\":\"quantityPerWindow\",\"argument\":\"amount\",\"quantity\":100,\"window\":60000}"
                  "the quantity per window"

              Expect.stringContains document "{\"clause\":\"dwell\",\"window\":500}" "the dwell"

              match Demanded.decode document with
              | Ok read -> Expect.equal read projection "reads back whole"
              | Error failure -> failtestf "the document does not read: %A" failure
          } ]

[<Tests>]
let tests =
    testList "Phase 2260 - effects limited over time windows by the host" [ limits; journal; demanded ]
