/// Phase 2438 (D58) — a server effect stage declares the quantities it spends,
/// and the demanded document prices them beside the leaves'.
///
/// The declaration is the REGISTRY's, by capability, beside the argument
/// policy (`ServerEffectRegistry.spends`): the shape a leaf declares (D54),
/// read as one performance's worst case. The document prices it per EVENT,
/// each call priced through the handler it reaches
/// (`Budget.quantityCostThrough`), so a repeat over a call multiplies what the
/// handler's effect stages and compute stages spend together. What is pinned
/// here: money and egress through effects, a compute stage and an effect stage
/// summed, the ceiling refusing before the first stage with nothing performed,
/// a unit mismatch reported rather than converted, and F1 — one device-shaped
/// effect priced statically AND decided at the gate's position by its argument
/// policy and a per-window count, each decision journaled and each admission
/// receipted.
module Fuaran.Program.Tests.EffectQuantityTests

open Expecto
open Fuaran.Core
open Fuaran.Program.Bounded
open Fuaran.Program.Server
open Fuaran.Program.Tests.ToyDomain

// ─── fixtures ────────────────────────────────────────────────────────────────

let private unitOf (text: string) : UnitOfMeasure =
    match Unit.parse text with
    | Ok unit -> unit
    | Error refusal -> failwithf "the test's unit does not parse: %A" refusal

/// Money in its minor unit: US cents.
let private cents = unitOf "c[USD]"

/// Egress. The Core unit algebra admits no information unit (`By` is not an
/// atom), so the count of bytes is declared dimensionless and the NAME says
/// what is counted (D58).
let private count = unitOf "1"

let private Spend = "api-spend"
let private Egress = "egress-bytes"

let private declared (name: string) (unit: UnitOfMeasure) (amount: int) : QuantityDeclaration =
    { Name = name
      Unit = unit
      Amount = amount }

let private ceiling (name: string) (unit: UnitOfMeasure) (bound: int) : QuantityCeiling =
    { Name = name
      Unit = unit
      Ceiling = bound }

/// A call whose closure throws if anything ever dispatches it: the gate prices
/// the tree and dispatches nothing.
let private calling (endpoint: string) : ToyAction =
    Ring(endpoint, false, (fun () -> failwith "the gate ran an action"))

let private treeOf (handlers: (string * ToyAction) list) : ToyNode =
    { Id = "root"
      Label = Const(JStr "root")
      Handlers = handlers
      Children =
        [ { Id = "heater"
            Label = Const(JStr "off")
            Handlers = []
            Children = [] } ] }

let private charge: Handler<ToyAction, ToyOp> =
    { Name = "charge"
      Stages = [ Effect(ServerEffect.HostCall("charge", JObj [ "amount", JInt 2 ], None)) ] }

let private upload: Handler<ToyAction, ToyOp> =
    { Name = "upload"
      Stages = [ Effect(ServerEffect.Notify("outbox", JStr "payload")) ] }

/// Counts every performance, so "nothing performed" is a number.
let private registryOf (performed: int ref) : ServerEffectRegistry =
    ServerEffectRegistry.denyAll
    |> ServerEffectRegistry.register "charge" (fun _ ->
        performed.Value <- performed.Value + 1
        Ok(JStr "charged"))
    |> ServerEffectRegistry.permissive
    |> ServerEffectRegistry.spends "host:charge" [ declared Spend cents 2 ]
    |> ServerEffectRegistry.spends "Notify" [ declared Egress count 4096 ]

let private servicesOf
    (registry: ServerEffectRegistry)
    (handlers: (string * Handler<ToyAction, ToyOp>) list)
    : ServerServices<ToyNode, ToyAction, ToyExpr, ToyStore, ToyOp, ToyEffect> =
    let services =
        handlers
        |> List.fold
            (fun services (endpoint, handler) -> ServerServices.withHandler endpoint handler services)
            (ServerServices.create witness)

    { services with
        Effects = registry
        CanDispatch = fun _ -> true }

let private covering (ceilings: QuantityCeiling list) : HostCoverage =
    HostCoverage.nothing
    |> HostCoverage.withEffects [ "Sound" ]
    |> HostCoverage.permissive
    |> HostCoverage.withQuantityCeilings ceilings

let private quantityFindings (findings: ServerStrictFinding list) : CoverageFinding list =
    findings
    |> List.choose (fun f ->
        match f with
        | ServerStrictFinding.Coverage(CoverageFinding.QuantityOverCeiling _ as finding)
        | ServerStrictFinding.Coverage(CoverageFinding.QuantityUnitMismatch _ as finding) -> Some finding
        | _ -> None)

let private strict
    (ceilings: QuantityCeiling list)
    (registry: ServerEffectRegistry)
    (handlers: (string * Handler<ToyAction, ToyOp>) list)
    (tree: ToyNode)
    =
    ServerSession.initStrict (covering ceilings) (servicesOf registry handlers) Map.empty tree

let private documented
    (registry: ServerEffectRegistry)
    (handlers: (string * Handler<ToyAction, ToyOp>) list)
    (tree: ToyNode)
    : QuantityDemand list =
    (ServerDemanded.ofTreeHandlersAndRegistry witness registry (Map.ofList handlers) tree).Quantities

let private demand (name: string) (unit: UnitOfMeasure) (worstCase: int) : QuantityDemand =
    { Name = name
      Unit = unit
      WorstCase = worstCase }

// ─── the declaration and the price ───────────────────────────────────────────

let private pricing =
    testList
        "an effect stage's declared quantities, priced"
        [ test "the registry holds the declaration by capability, replaced rather than accumulated" {
              let registry =
                  ServerEffectRegistry.denyAll
                  |> ServerEffectRegistry.spends "host:charge" [ declared Spend cents 1 ]
                  |> ServerEffectRegistry.spends "host:charge" [ declared Spend cents 2 ]

              Expect.equal
                  (ServerEffectRegistry.quantitiesFor "host:charge" registry)
                  [ declared Spend cents 2 ]
                  "the second declaration replaces the first"

              Expect.isEmpty
                  (ServerEffectRegistry.quantitiesFor "Notify" registry)
                  "an undeclared capability spends nothing"
          }

          test "money: 2 cents per call, performed by a repeat bounded at 50, prices 100" {
              let tree = treeOf [ "press", Times(Bound.Literal 50, calling "/charge") ]

              Expect.equal
                  (documented (registryOf (ref 0)) [ "/charge", charge ] tree)
                  [ demand Spend cents 100 ]
                  "the repeat multiplies the effect stage's declared spend"
          }

          test "egress: 4096 bytes per notification, over an Each of three, prices 12288" {
              let tree =
                  treeOf [ "send", ForEach([ JInt 1; JInt 2; JInt 3 ], "x", calling "/upload") ]

              Expect.equal
                  (documented (registryOf (ref 0)) [ "/upload", upload ] tree)
                  [ demand Egress count 12288 ]
                  "the iteration multiplies the effect stage's declared egress"
          }

          test "a compute stage and an effect stage spending the same pair are summed in the handler" {
              let heat: Handler<ToyAction, ToyOp> =
                  { Name = "heat"
                    Stages = [ Compute(Beep 5); Effect(ServerEffect.HostCall("charge", JObj [], None)) ] }

              let registry =
                  registryOf (ref 0)
                  |> ServerEffectRegistry.spends "host:charge" [ declared beepMinutes minute 7 ]

              Expect.equal
                  (documented registry [ "/heat", heat ] (treeOf [ "press", calling "/heat" ]))
                  [ demand beepMinutes minute 12 ]
                  "5 from the leaf, 7 from the effect, one call"

              Expect.equal
                  (documented registry [ "/heat", heat ] (treeOf [ "press", Seq [ Beep 3; calling "/heat" ] ]))
                  [ demand beepMinutes minute 15 ]
                  "and the tree's own leaf beside them"
          }

          test "a negative declared amount prices as nothing and buys down nothing" {
              let registry =
                  registryOf (ref 0)
                  |> ServerEffectRegistry.spends "host:charge" [ declared Spend cents -5 ]

              Expect.equal
                  (documented registry [ "/charge", charge ] (treeOf [ "press", Seq [ calling "/charge" ] ]))
                  [ demand Spend cents 0 ]
                  "the pair is declared, at nothing"
          }

          test "one event runs one action: two actions price at the dearer, not the sum" {
              let tree =
                  treeOf
                      [ "once", calling "/charge"
                        "thrice", Times(Bound.Literal 3, calling "/charge") ]

              Expect.equal
                  (documented (registryOf (ref 0)) [ "/charge", charge ] tree)
                  [ demand Spend cents 6 ]
                  "the dearer event"
          }

          test "a compute stage reached through a repeat is multiplied too, registry or not" {
              let beeping: Handler<ToyAction, ToyOp> =
                  { Name = "beeping"
                    Stages = [ Compute(Beep 4) ] }

              let tree = treeOf [ "press", Times(Bound.Literal 3, calling "/beep") ]

              Expect.equal
                  (ServerDemanded.ofTreeAndHandlers witness (Map.ofList [ "/beep", beeping ]) tree).Quantities
                  [ demand beepMinutes minute 12 ]
                  "three calls, four each — summing the handler once would have read 4"
          }

          test "the registry-free walk prices no effect stage: the declaration is the registry's" {
              let tree = treeOf [ "press", calling "/charge" ]

              Expect.isEmpty
                  (ServerDemanded.ofTreeAndHandlers witness (Map.ofList [ "/charge", charge ]) tree).Quantities
                  "no registry, no effect quantity"
          }

          test "a call naming no handler, and a call inside a called handler, spend nothing" {
              let relaying: Handler<ToyAction, ToyOp> =
                  { Name = "relaying"
                    Stages = [ Compute(calling "/charge") ] }

              let registry = registryOf (ref 0)

              Expect.isEmpty
                  (documented registry [ "/charge", charge ] (treeOf [ "press", calling "/nobody" ]))
                  "an unregistered endpoint reaches nothing"

              Expect.isEmpty
                  (documented registry [ "/relay", relaying; "/charge", charge ] (treeOf [ "press", calling "/relay" ]))
                  "one hop: the stage's call runs against the inert arm"
          } ]

// ─── the ceiling, before the first stage ─────────────────────────────────────

let private gating =
    testList
        "the ceiling decides before the first stage"
        [ test "a ceiling of 50 cents refuses the 100-cent program, and nothing is performed" {
              let performed = ref 0
              let tree = treeOf [ "press", Times(Bound.Literal 50, calling "/charge") ]

              match strict [ ceiling Spend cents 50 ] (registryOf performed) [ "/charge", charge ] tree with
              | Ok _ -> failtest "the over-ceiling program was admitted"
              | Error findings ->
                  Expect.equal
                      (quantityFindings findings)
                      [ CoverageFinding.QuantityOverCeiling(Spend, "c[USD]", 100, 50) ]
                      "refused with the figure"

              Expect.equal performed.Value 0 "nothing was performed"

              Expect.isOk
                  (strict [ ceiling Spend cents 100 ] (registryOf performed) [ "/charge", charge ] tree)
                  "admitted at its own worst case"
          }

          test "an egress ceiling refuses the same way" {
              let tree =
                  treeOf [ "send", ForEach([ JInt 1; JInt 2; JInt 3 ], "x", calling "/upload") ]

              match strict [ ceiling Egress count 8192 ] (registryOf (ref 0)) [ "/upload", upload ] tree with
              | Ok _ -> failtest "the over-ceiling program was admitted"
              | Error findings ->
                  Expect.equal
                      (quantityFindings findings)
                      [ CoverageFinding.QuantityOverCeiling(Egress, "1", 12288, 8192) ]
                      "refused with the figure"
          }

          test "a ceiling in another unit is reported, never converted" {
              let tree = treeOf [ "press", calling "/charge" ]

              match strict [ ceiling Spend (unitOf "[USD]") 1 ] (registryOf (ref 0)) [ "/charge", charge ] tree with
              | Ok _ -> failtest "a mismatched ceiling was read as a bound"
              | Error findings ->
                  Expect.equal
                      (quantityFindings findings)
                      [ CoverageFinding.QuantityUnitMismatch(Spend, "c[USD]", "[USD]") ]
                      "the unit mismatch, with both units named"
          } ]

// ─── F1: one effect, every gate ──────────────────────────────────────────────

/// A host clock the test turns by hand.
type private Clock() =
    member val Now = 0L with get, set

    member this.Services(journal: EffectJournal) : DurableServices =
        DurableServices.create
        |> DurableServices.withJournal journal
        |> DurableServices.withClock (fun () -> this.Now)

let private HeaterMinutes = "heater-minutes"

/// The device-shaped effect: an actuation as an op, so it rides `ApplyOps` —
/// the arm the argument policy, the time windows and the receipts already
/// decide — and the registry prices it.
let private heatWith (target: string) : Handler<ToyAction, ToyOp> =
    { Name = "heat"
      Stages = [ Effect(ServerEffect.ApplyOps [ Relabel(target, "on") ]) ] }

/// The device's whole policy on one capability, declared once: the quantity
/// one actuation spends, the targets it may reach, and one per window.
let private deviceRegistry: ServerEffectRegistry =
    ServerEffectRegistry.denyAll
    |> ServerEffectRegistry.permissive
    |> ServerEffectRegistry.spends "ApplyOps" [ declared HeaterMinutes minute 15 ]
    |> ServerEffectRegistry.constrain
        "ApplyOps"
        [ ServerConstraintClause.AllowList("target", [ "heater" ])
          ServerConstraintClause.PerWindow(1, 1000) ]

/// The performer: the actuation's receipt is the write it performed.
let private actuating (performed: int ref) : OpPerformance<ToyNode, ToyOp> =
    OpPerformance.performedBy (fun _ op ->
        performed.Value <- performed.Value + 1

        match op with
        | Relabel(id, label) -> Ok(OpReceipt.ofWrites [ WriteReceipt.ofText id label ]))

let private device =
    testList
        "F1 - one device effect: priced, policed, windowed and receipted at one gate"
        [ test "the static price refuses two actuations under a 20-minute ceiling and admits one" {
              let handlers = [ "/heat", heatWith "heater" ]

              match
                  strict
                      [ ceiling HeaterMinutes minute 20 ]
                      deviceRegistry
                      handlers
                      (treeOf [ "press", Times(Bound.Literal 2, calling "/heat") ])
              with
              | Ok _ -> failtest "two 15-minute actuations were admitted under 20"
              | Error findings ->
                  Expect.equal
                      (quantityFindings findings)
                      [ CoverageFinding.QuantityOverCeiling(HeaterMinutes, "min", 30, 20) ]
                      "refused before the first stage"

              Expect.isOk
                  (strict
                      [ ceiling HeaterMinutes minute 20 ]
                      deviceRegistry
                      handlers
                      (treeOf [ "press", calling "/heat" ]))
                  "one actuation is within the ceiling"
          }

          test "at the gate: an admission receipted, a window refusal and a policy refusal, each journaled" {
              let performed = ref 0
              let clock = Clock()
              let journal = Journal.inMemory ()

              let store: ServerStore<ToyNode, ToyStore> =
                  { Tree = treeOf []
                    Bindings = Map.empty }

              let run invocation handler (from: ServerStore<ToyNode, ToyStore>) =
                  Durable.runWith
                      witness
                      (clock.Services journal)
                      invocation
                      deviceRegistry
                      (actuating performed)
                      Fuaran.Compute.DataFrame.noResolve
                      "node"
                      handler
                      from

              let admitted = run "i0" (heatWith "heater") store
              Expect.isTrue admitted.Outcome.Committed "the first actuation is admitted"

              Expect.equal
                  admitted.Outcome.Receipts
                  [ OpReceipt.ofWrites [ WriteReceipt.ofText "heater" "on" ] ]
                  "and receipted with the write it performed"

              clock.Now <- 10L
              let windowed = run "i1" (heatWith "heater") admitted.Outcome.Store
              Expect.isFalse windowed.Outcome.Committed "a second actuation inside the window is refused"

              let offList = run "i2" (heatWith "door") admitted.Outcome.Store
              Expect.isFalse offList.Outcome.Committed "an actuation the policy does not admit is refused"

              let reasons (outcome: DurableOutcome<ToyNode, ToyStore, ToyOp, ToyEffect>) =
                  outcome.Outcome.Diagnostics
                  |> List.choose (fun d ->
                      match d with
                      | ServerDiagnostic.Failed(capability, reason) -> Some(capability, reason)
                      | _ -> None)

              Expect.equal
                  (reasons windowed)
                  [ "ApplyOps", ServerArgumentPolicy.describe (ServerConstraintDefect.OverWindow(1, 1000)) ]
                  "the window refused, naming the declaration"

              Expect.equal
                  (reasons offList)
                  [ "ApplyOps", ServerArgumentPolicy.describe (ServerConstraintDefect.OffList "target") ]
                  "the allow-list refused, naming the argument"

              Expect.equal performed.Value 1 "only the admission was performed"

              // The admission: the window's decision at its ordinal, then the
              // performed actuation, whose journaled value is its receipt.
              let admission = journal.Read "i0"

              Expect.equal
                  (Journal.describe admission |> List.take 4)
                  [ "0 ReadClock attempted"
                    "0 ReadClock completed"
                    "1 Limit ApplyOps attempted"
                    "1 Limit ApplyOps completed" ]
                  "the admission is journaled at its ordinal"

              Expect.equal
                  (admission
                   |> List.choose (fun e ->
                       match e.Step, e.Phase with
                       | 2, JournalPhase.Completed value -> Some(OpReceipt.decode value)
                       | _ -> None))
                  [ Ok(OpReceipt.ofWrites [ WriteReceipt.ofText "heater" "on" ]) ]
                  "the actuation's journaled value is its receipt"

              Expect.equal
                  (Journal.describe (journal.Read "i1"))
                  [ "0 ReadClock attempted"
                    "0 ReadClock completed"
                    "1 Limit ApplyOps attempted"
                    "1 Limit ApplyOps refused"
                    "-1 Invocation completed" ]
                  "the window refusal is journaled at its ordinal, and nothing after it ran"

              // The policy refusal is a function of the plan and the declared
              // clauses alone, so the journal records the invocation and a
              // replay recomputes the refusal rather than reading it (D52's
              // reading: only what a clock or a counter decided is recorded).
              Expect.equal
                  (Journal.describe (journal.Read "i2"))
                  [ "-1 Invocation completed" ]
                  "the policy-refused invocation is journaled complete"

              let replayed = run "i2" (heatWith "door") admitted.Outcome.Store
              Expect.equal (reasons replayed) (reasons offList) "a replay refuses it again"
              Expect.equal performed.Value 1 "and performs nothing"
          } ]

[<Tests>]
let tests =
    testList "Phase 2438 - a server effect stage declares the quantities it spends" [ pricing; gating; device ]
