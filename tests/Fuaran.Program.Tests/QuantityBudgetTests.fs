/// Phase 2261 — a domain declares a quantity per leaf, and the budget prices
/// its worst case before the program runs.
///
/// The toy's `Beep volume` declares `beep-minutes` in minutes (`ToyDomain`).
/// What is tested here is the path from that declaration to a refusal: the
/// price (`Budget.quantityCost`, D35's rules without the step), the demanded
/// document carrying it (version 13, `quantities`), a host's ceiling on it
/// (`HostCoverage.withQuantityCeilings`) and the finding the gate answers
/// BEFORE anything runs — the acceptance's worked example first. The proof
/// oracle's differential over the same price is `ToyBudgetOracleTests`.
module Fuaran.Program.Tests.QuantityBudgetTests

open Expecto
open Fuaran.Core
open Fuaran.Program.Bounded
open Fuaran.Program.Tests.ToyDomain

let private minutes (name: string) (ceiling: int) : QuantityCeiling =
    { Name = name
      Unit = minute
      Ceiling = ceiling }

let private hour: UnitOfMeasure =
    match Unit.parse "h" with
    | Ok unit -> unit
    | Error refusal -> failwithf "the test's unit does not parse: %A" refusal

/// The acceptance's worked example: a leaf spending 30, a repeat of 3 over a
/// leaf spending 20, and a choice between a leaf spending 45 and nothing —
/// 30 + 3 × 20 + max(45, 0) = 135.
let private workedExample: ToyAction =
    Seq
        [ Beep 30
          Times(Bound.Literal 3, Beep 20)
          Pick(Missing, Beep 45, Seq [], None) ]

/// A tree carrying one handler, and a call whose closure throws if anything
/// ever dispatches it — the gate prices the tree and dispatches nothing.
let private treeOf (handlers: (string * ToyAction) list) : ToyNode =
    { Id = "root"
      Label = Const(JStr "root")
      Handlers =
        handlers
        @ [ "never", Ring("/never", false, fun () -> failwith "the gate ran an action") ]
      Children = [] }

let private covering: HostCoverage =
    HostCoverage.nothing
    |> HostCoverage.withEffects [ "Sound" ]
    |> HostCoverage.permissive

let private quantityFindings (coverage: HostCoverage) (tree: ToyNode) : CoverageFinding list =
    Demanded.check witness coverage tree
    |> List.filter (fun f ->
        match f with
        | CoverageFinding.QuantityOverCeiling _
        | CoverageFinding.QuantityUnitMismatch _ -> true
        | _ -> false)

let private price (action: ToyAction) : int =
    Budget.quantityCost witness beepMinutes minute action

let private pricing =
    testList
        "the price"
        [ test "the worked example prices as stated: 30 + 3 x 20 + max(45, 0) = 135" {
              Expect.equal (price workedExample) 135 "the worked example"
          }

          test "a two-arm choice is priced by its dearer arm, whichever arm it is" {
              Expect.equal (price (Pick(Missing, Beep 45, Hush, None))) 45 "the true arm dearer"
              Expect.equal (price (Pick(Missing, Beep 10, Seq [ Beep 20; Beep 30 ], None))) 50 "the false arm dearer"
              Expect.equal (price (Pick(Missing, Hush, Hush, None))) 0 "no arm spends"
          }

          test "a nested repeat multiplies through, a parameter bound at the top of its range" {
              Expect.equal
                  (price (Times(Bound.Literal 2, Times(Bound.Parameter(Read "n", 0, 3), Beep 5))))
                  30
                  "2 x 3 x 5"

              Expect.equal (price (Times(Bound.Literal -1, Beep 5))) 0 "a negative count runs nothing"
          }

          test "an Each spends its body once per element, and a stored one its body at its ceiling" {
              Expect.equal (price (ForEach([ JInt 1; JInt 2; JInt 3 ], "x", Beep 4))) 12 "three elements"
              Expect.equal (price (ForEachOf(Read "xs", 5, "x", Beep 2))) 10 "at most five"
              Expect.equal (price (ForEach([], "x", Beep 4))) 0 "no elements"
          }

          test "a step is not a quantity: the condition, the bound and the read spend nothing" {
              Expect.equal (price (Pick(Missing, Seq [], Seq [], None))) 0 "a choice over nothing"
              Expect.equal (price (Times(Bound.Literal 1000, Hush))) 0 "a repeat of a leaf spending nothing"
              Expect.equal (price (ForEachOf(Read "xs", 1000, "x", Hush))) 0 "a read of a stored collection"

              Expect.equal
                  (Budget.actionCascadeCost witness (Times(Bound.Literal 1000, Hush)))
                  1001
                  "the cascade still counts steps"
          }

          test "a quantity under another name or unit is not this one" {
              Expect.equal (Budget.quantityCost witness "heater-minutes" minute workedExample) 0 "another name"
              Expect.equal (Budget.quantityCost witness beepMinutes hour workedExample) 0 "another unit"

              Expect.equal
                  (Budget.declaredQuantities witness workedExample)
                  [ beepMinutes, minute ]
                  "the one pair the leaves declare, once"

              Expect.isEmpty (Budget.declaredQuantities witness (Seq [ Hush; Need Missing ])) "nothing declared"
          }

          test "the price saturates rather than wrapping" {
              Expect.equal
                  (price (Times(Bound.Literal System.Int32.MaxValue, Beep 2)))
                  System.Int32.MaxValue
                  "a product past the bound reads as the bound"
          } ]

let private document =
    testList
        "the demanded document"
        [ test "a tree's worst case is its dearest handler's; a union of projections sums" {
              let tree = treeOf [ "a", Beep 30; "b", Seq [ Beep 20; Beep 30 ] ]
              let projection = Demanded.ofTree witness tree

              Expect.equal
                  projection.Quantities
                  [ { Name = beepMinutes
                      Unit = minute
                      WorstCase = 50 } ]
                  "one event reaches one handler: the max over the two"

              let joined =
                  Demanded.union [ Demanded.ofAction witness (Beep 30); Demanded.ofAction witness (Beep 50) ]

              Expect.equal
                  (joined.Quantities |> List.map _.WorstCase)
                  [ 80 ]
                  "what is joined runs together: the sum, which is a bound either way"
          }

          test "the document carries the quantities (since version 13) and reads back whole" {
              let projection = Demanded.ofTree witness (treeOf [ "run", workedExample ])
              let encoded = Demanded.encode projection

              Expect.equal Demanded.Version 14 "the version Phase 2262 moved it to; the quantities rode 13"
              Expect.stringContains encoded "\"version\":14" "carried in the document"

              Expect.stringContains
                  encoded
                  "\"quantities\":[{\"name\":\"beep-minutes\",\"unit\":\"min\",\"worstCase\":135}]"
                  "the worst case, with its unit as the algebra renders it"

              match Demanded.decode encoded with
              | Ok read -> Expect.equal read projection "reads back whole"
              | Error failure -> failtestf "the document does not read: %A" failure
          }

          test "a program spending nothing carries an empty member, never an absent one" {
              let encoded = Demanded.encode (Demanded.ofTree witness (treeOf [ "run", Hush ]))
              Expect.stringContains encoded "\"quantities\":[]" "empty, present"
          }

          test "a document without the member is refused, and so is a unit the algebra does not read" {
              let encoded =
                  Demanded.encode (Demanded.ofTree witness (treeOf [ "run", workedExample ]))

              match
                  Demanded.decode (
                      encoded.Replace(
                          ",\"quantities\":[{\"name\":\"beep-minutes\",\"unit\":\"min\",\"worstCase\":135}]",
                          ""
                      )
                  )
              with
              | Error failure ->
                  Expect.equal failure.Defect DemandedDefect.MissingMember "the member is required"
                  Expect.equal failure.Field "quantities" "named"
              | Ok _ -> failtest "a document predating the quantities read as one that priced them"

              match Demanded.decode (encoded.Replace("\"unit\":\"min\"", "\"unit\":\"furlongs-per-fortnight\"")) with
              | Error failure ->
                  Expect.equal failure.Defect DemandedDefect.WrongType "not a unit"
                  Expect.equal failure.Field "quantities[0].unit" "at the unit"
              | Ok _ -> failtest "a unit the algebra refuses was read"
          } ]

let private gate =
    testList
        "the gate"
        [ test "a 120 ceiling refuses the worked example with the figure, and nothing has run" {
              let coverage =
                  covering |> HostCoverage.withQuantityCeilings [ minutes beepMinutes 120 ]

              Expect.equal
                  (quantityFindings coverage (treeOf [ "run", workedExample ]))
                  [ CoverageFinding.QuantityOverCeiling(beepMinutes, "min", 135, 120) ]
                  "refused before the first stage, naming the worst case and the ceiling"
          }

          test "a ceiling the worst case meets admits the program" {
              let coverage =
                  covering |> HostCoverage.withQuantityCeilings [ minutes beepMinutes 135 ]

              Expect.isEmpty (quantityFindings coverage (treeOf [ "run", workedExample ])) "135 of 135 is within"
          }

          test "a quantity nobody bounded is unconstrained, and a ceiling nobody spends against is silent" {
              Expect.isEmpty (quantityFindings covering (treeOf [ "run", workedExample ])) "no ceiling declared"

              let other =
                  covering |> HostCoverage.withQuantityCeilings [ minutes "heater-minutes" 1 ]

              Expect.isEmpty (quantityFindings other (treeOf [ "run", workedExample ])) "a ceiling on another quantity"

              Expect.isEmpty
                  (quantityFindings
                      (covering |> HostCoverage.withQuantityCeilings [ minutes beepMinutes 0 ])
                      (treeOf [ "run", Hush ]))
                  "nothing spent under a zero ceiling"
          }

          test "a ceiling in another unit is reported, never scaled" {
              let coverage =
                  covering
                  |> HostCoverage.withQuantityCeilings
                      [ { Name = beepMinutes
                          Unit = hour
                          Ceiling = 1000 } ]

              Expect.equal
                  (quantityFindings coverage (treeOf [ "run", workedExample ]))
                  [ CoverageFinding.QuantityUnitMismatch(beepMinutes, "min", "h") ]
                  "1000 h would admit; the gate converts nothing and says so"
          }

          test "the finding is ordered after the server tier and says what it is" {
              let described =
                  Demanded.describe (CoverageFinding.QuantityOverCeiling(beepMinutes, "min", 135, 120))

              Expect.stringContains described "135 min" "the worst case"
              Expect.stringContains described "120 min" "the ceiling"
              Expect.stringContains described "before the first stage" "when"

              let coverage =
                  HostCoverage.nothing
                  |> HostCoverage.withQuantityCeilings [ minutes beepMinutes 120 ]

              match Demanded.check witness coverage (treeOf [ "run", workedExample ]) with
              | [ CoverageFinding.UnregisteredEffect "Sound"; CoverageFinding.QuantityOverCeiling _ ] -> ()
              | findings -> failtestf "the effect finding leads and the quantity finding closes: %A" findings
          } ]

[<Tests>]
let tests =
    testList "Phase 2261 - a declared quantity priced before the program runs" [ pricing; document; gate ]
