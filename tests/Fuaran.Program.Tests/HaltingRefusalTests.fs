/// Phase 2441 — a witness DECLARES how its refusals read, and under the halting
/// reading a run is all or nothing. The two toy witnesses differ in nothing
/// but that declaration (`ToyDomain.witness` continues, `ToyDomain.halting`
/// halts), so every case below runs ONE program through both and reads the
/// difference as the declaration's. The model this measures is
/// `proofs/BoundedFold.fst` section 12 (`halting_run_all_or_nothing`,
/// `continuing_run_is_fold`); the differential host for it is in
/// `ToyBoundedFoldOracleTests`, which runs the extraction beside the core at
/// the halting witness over the whole toy corpus.
module Fuaran.Program.Tests.HaltingRefusalTests

open Expecto
open Fuaran.Core
open Fuaran.Program.Bounded
open Fuaran.Program.Tests.ToyDomain

let private noCall =
    fun () -> failwith "the core invoked a closure a carried action holds"

let private continuing (action: ToyAction) (store: ToyStore) =
    BoundedActions.runInert witness "n1" action store

let private halting (action: ToyAction) (store: ToyStore) =
    BoundedActions.runInert ToyDomain.halting "n1" action store

/// The last diagnostic of an outcome, which a halted run under the halting
/// reading ends with the refusal that halted it (the model's
/// `halted_ends_with_refusal`).
let private last (outcome: BoundedOutcome<ToyStore, ToyEffect>) = outcome.Diagnostics |> List.tryLast

/// Two leaves admitted, a third refused, two more that would have run: the
/// shard's own case.
let private thirdLeafRefuses =
    Seq
        [ Put("before", Some(JStr "1"), None)
          Beep 1
          Beep 2
          Beep 11
          Beep 3
          Put("after", Some(JStr "2"), None) ]

[<Tests>]
let tests =
    testList
        "Phase 2441 - the witness's declared reading of a refusal"
        [ test
              "a halting witness whose third leaf refuses emits nothing, keeps the entry store, and names the leaf last" {
              let entry = Map.ofList [ "title", JStr "t" ]
              let outcome = halting thirdLeafRefuses entry

              Expect.isTrue outcome.Halted "the refused leaf halted the run"
              Expect.isEmpty outcome.Effects "NOTHING was emitted — not the two beeps that were admitted before it"

              Expect.equal
                  outcome.Store
                  entry
                  "the run settled to the ENTRY store — the write before the leaf is gone too"

              Expect.equal
                  outcome.Diagnostics
                  [ BoundedDiagnostic.Refused("n1", "Beep(11)", "volume 11 is above the ceiling") ]
                  "the outcome names the refused leaf, by node and description, and nothing after it ran"

              Expect.equal
                  (last outcome)
                  (Some(BoundedDiagnostic.Refused("n1", "Beep(11)", "volume 11 is above the ceiling")))
                  "the refusal is the last word"
          }

          test "a non-halting witness keeps the prefix as today, byte for byte" {
              let entry = Map.ofList [ "title", JStr "t" ]
              let outcome = continuing thirdLeafRefuses entry

              Expect.isFalse outcome.Halted "today's reading: a refusal does not halt"

              Expect.equal
                  outcome.Effects
                  [ Sound("n1", 1); Sound("n1", 2); Sound("n1", 3) ]
                  "every admitted leaf's effect stands, before AND after the refusal"

              Expect.equal
                  (outcome.Store |> Map.toList)
                  [ "after", JStr "2"; "before", JStr "1"; "title", JStr "t" ]
                  "both writes landed"

              Expect.equal
                  outcome.Diagnostics
                  [ BoundedDiagnostic.Refused("n1", "Beep(11)", "volume 11 is above the ceiling") ]
                  "the refusal is a diagnostic the sequence carried on past"
          }

          test "the refused leaf's POSITION is the traced run's length: the members that ran, the refused one last" {
              // The outcome names the leaf by description; the trace of a
              // reversible run says WHERE it sat — one entry per member that
              // ran, so the halting leaf is the last entry and its ordinal is
              // the trace's length.
              let outcome, _, trace =
                  BoundedActions.runTraced ToyDomain.halting HandlerArm.inert "n1" thirdLeafRefuses Map.empty ()

              Expect.isTrue outcome.Halted "halted"
              Expect.isEmpty outcome.Effects "the traced run settles exactly as the run does (traced_run_settles_alike)"
              Expect.equal outcome.Store Map.empty "the entry store"

              match trace with
              | Trace.Seq steps ->
                  Expect.equal
                      (List.length steps)
                      4
                      "the write, two beeps and the refused beep ran — it was the fourth member"
              | other -> failtestf "expected the sequence's trace, got %A" other
          }

          test "the fold's OWN refusals halt under the halting reading too, and continue under today's" {
              // A reserved-key write, a write whose source did not resolve, a
              // write whose source errored, and a call declaring a result
              // target: the four refusals the fold produces without asking
              // the witness. Each sits between two admitted leaves.
              let cases =
                  [ "reserved key",
                    Put("sys.secret", Some(JStr "no"), None),
                    "State key 'sys.secret' is under the host-reserved 'sys.' namespace"
                    "unresolved source",
                    Put("c", None, Some Missing),
                    "valueFrom did not resolve to a value — no write performed"
                    "errored source", Put("d", None, Some(Fail "boom")), "valueFrom errored: boom — no write performed"
                    "declared result target",
                    Ring("/targeted", true, noCall),
                    "the call declares a result target; a handler declares where its own results land" ]

              for label, refusing, reason in cases do
                  let program = Seq [ Beep 1; refusing; Beep 2 ]
                  let halted = halting program Map.empty

                  Expect.isTrue halted.Halted (label + ": halts")
                  Expect.isEmpty halted.Effects (label + ": nothing emitted, not even the beep before it")
                  Expect.equal halted.Store Map.empty (label + ": the entry store")

                  match last halted with
                  | Some(BoundedDiagnostic.Refused(_, _, r)) ->
                      Expect.equal r reason (label + ": the refusal is the last word")
                  | other -> failtestf "%s: expected the refusal last, got %A" label other

                  let continued = continuing program Map.empty
                  Expect.isFalse continued.Halted (label + ": today's reading carries on")
                  Expect.equal continued.Effects [ Sound("n1", 1); Sound("n1", 2) ] (label + ": both beeps stand")
          }

          test "a guard halt and a flow halt settle under the halting reading, and keep the prefix under today's" {
              // The halting reading makes the RUN atomic, whatever halted it:
              // a guard that does not hold, a branch that cannot decide, a
              // repeat over its bound. Under today's reading the prefix stands
              // (GenericityTests pins that), and the handler rolls back (D8).
              let halts =
                  [ "guard", Need(Const(JBool false))
                    "undecidable branch", Pick(Missing, Beep 2, Beep 3, None)
                    "over-bound repeat", Times(Bound.Parameter(Const(JInt 9), 0, 3), Beep 2) ]

              for label, stopper in halts do
                  let program = Seq [ Put("before", Some(JStr "1"), None); Beep 1; stopper; Beep 4 ]

                  let settled = halting program Map.empty
                  Expect.isTrue settled.Halted (label + ": halted")
                  Expect.isEmpty settled.Effects (label + ": nothing emitted")
                  Expect.equal settled.Store Map.empty (label + ": the write before the halt is gone — all or nothing")

                  let kept = continuing program Map.empty
                  Expect.isTrue kept.Halted (label + ": halted under today's reading too")
                  Expect.equal kept.Effects [ Sound("n1", 1) ] (label + ": the prefix's effect stands")

                  Expect.equal
                      (kept.Store |> Map.toList)
                      [ "before", JStr "1" ]
                      (label + ": the write before the halt stands")
          }

          test "a run every step of which was admitted is identical under both readings" {
              let program =
                  Seq
                      [ Put("a", Some(JStr "literal"), None)
                        Put("b", None, Some(Read "a"))
                        Beep 3
                        Hush
                        Ring("/nowhere", false, noCall)
                        Pick(Const(JBool true), Beep 4, Beep 5, Some(Const(JBool true)))
                        Times(Bound.Literal 2, Beep 6)
                        ForEach([ JInt 1; JInt 2 ], "x", Beep 7) ]

              let today = continuing program Map.empty
              let declared = halting program Map.empty

              Expect.isFalse declared.Halted "nothing refused, nothing halted"
              Expect.equal declared today "the declaration changes nothing about a run it never had to settle"
              Expect.isNonEmpty declared.Effects "and the run did something to compare"

              Expect.equal
                  (declared.Diagnostics
                   |> List.filter (fun d ->
                       match d with
                       | BoundedDiagnostic.Refused _ -> true
                       | _ -> false))
                  []
                  "an unhalted run under the halting reading met no refusal (halting_unhalted_is_refusal_free) — its diagnostics are declines"
          }

          test
              "a witness declaring Continues never halts on a refusal — the reading the UI tier declares (ui_never_halts)" {
              // Every refusal the fold and the toy leaf can produce, in one
              // program, under today's reading: diagnosed, never halted. This
              // is the behaviour the UI tier's witness keeps unchanged by
              // declaring `Continues`, and what `GenericityTests` pinned
              // before the declaration existed.
              let outcome =
                  continuing
                      (Seq
                          [ Beep 11
                            Put("sys.secret", Some(JStr "no"), None)
                            Put("c", None, Some Missing)
                            Put("d", None, Some(Fail "boom"))
                            Ring("/targeted", true, noCall)
                            Beep 1 ])
                      Map.empty

              Expect.isFalse outcome.Halted "no refusal halts under Continues"
              Expect.equal (List.length outcome.Diagnostics) 5 "every refusal is diagnosed"
              Expect.equal outcome.Effects [ Sound("n1", 1) ] "and the leaf after them all still runs"
          }

          test "a scope refusal at the fold's entry settles the same way under both readings: nothing ran" {
              let illScoped = Seq [ Beep 1; Put("x", None, Some(Hole "unbound")) ]

              for label, run in [ "continuing", continuing; "halting", halting ] do
                  let outcome = run illScoped Map.empty
                  Expect.isTrue outcome.Halted (label + ": refused at entry")
                  Expect.isEmpty outcome.Effects (label + ": nothing ran")
                  Expect.equal outcome.Store Map.empty (label + ": nothing written")
          } ]
