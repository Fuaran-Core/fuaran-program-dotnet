module Fuaran.Program.Tests.BoundedArgumentPolicyTests

// ─── The argument-policy check, beside its clauses (Phase 2440, D59) ─
//
// The check is a pure function of the declared clauses and what one effect
// carries, so it lives in `Fuaran.Program.Bounded` beside
// `ServerConstraintClause`, and a leaf-gating witness decides a leaf's
// arguments with no server package in sight. This file opens ONLY the
// substrate and `Fuaran.Program.Bounded`, and reproduces, against
// `ArgumentPolicy.check`, every argument-policy case `AtMostTests` and
// `ArgumentFloorTests` assert through the server placement — the same
// refusals, token for token. `ArgumentFloorTests` holds the differential that
// the server's check IS this check.

open Expecto
open Fuaran.Core
open Fuaran.Program.Bounded

/// A leaf witness's call: the host call's argument object read on the one
/// shared reading, its canonical bytes as the ceiling's measure, and no clock.
let private decide (clauses: ServerConstraintClause list) (args: (string * JVal) list) =
    let arguments = JObj args

    ArgumentPolicy.check
        WindowedLimiter.unjudgeable
        "host:heat"
        clauses
        (ArgumentPolicy.ofObject arguments)
        (System.Text.Encoding.UTF8.GetByteCount(ProgramWire.render arguments))

let private ceiling =
    testList
        "AtMost — reproduced from the server placement's cases (Phase 1982)"
        [ test "an integer argument is read as a number, and a string one only in its canonical spelling" {
              let five = [ ServerConstraintClause.AtMost("n", 5) ]

              for args, expected in
                  [ [ "n", JInt 5 ], true
                    [ "n", JInt 6 ], false
                    [ "n", JInt -3 ], true
                    [ "n", JStr "5" ], true
                    [ "n", JStr "-2" ], true
                    [ "n", JStr "05" ], false
                    [ "n", JStr "5.0" ], false
                    [ "n", JStr " 5" ], false
                    [ "n", JStr "-0" ], false
                    [ "n", JStr "+5" ], false
                    [ "n", JStr "five" ], false
                    [ "n", JStr "9999999999999999999" ], false
                    [ "other", JInt 100 ], true
                    [], true ] do
                  let verdict = decide five args
                  Expect.equal (Result.isOk verdict) expected $"%A{args}"

                  if not expected then
                      Expect.equal verdict (Error(ServerConstraintDefect.OffList "n")) "the allow-list's token"
          }

          test "AtMost(count, 90) admits 90 and refuses 91, naming the argument and never the value" {
              let ninety = [ ServerConstraintClause.AtMost("count", 90) ]
              Expect.isOk (decide ninety [ "count", JInt 90 ]) "90 is at the limit"

              Expect.equal
                  (decide ninety [ "count", JInt 91 ] |> Result.mapError ArgumentPolicy.describe)
                  (Error "argument-not-allowed:count")
                  "91 is over it"
          }

          test "an integer member binds an allow-list on its name" {
              let one = [ ServerConstraintClause.AllowList("n", [ "1" ]) ]
              Expect.isOk (decide one [ "n", JInt 1 ]) "the permitted number"
              Expect.isError (decide one [ "n", JInt 2 ]) "an unpermitted number is seen, and refused"
          } ]

let private floor =
    testList
        "AtLeast — reproduced from the server placement's cases (Phase 2262)"
        [ test "present arguments: at and above the floor admit, below it refuses under the argument" {
              let one = [ ServerConstraintClause.AtLeast("n", 1) ]

              for args, expected in
                  [ [ "n", JInt 1 ], true
                    [ "n", JInt 90 ], true
                    [ "n", JInt 0 ], false
                    [ "n", JInt -1 ], false
                    [ "n", JStr "1" ], true
                    [ "n", JStr "0" ], false ] do
                  let verdict = decide one args
                  Expect.equal (Result.isOk verdict) expected $"%A{args}"

                  if not expected then
                      Expect.equal verdict (Error(ServerConstraintDefect.OffList "n")) "the allow-list's token"
          }

          test "a non-integer value is refused, in every spelling AtMost refuses" {
              let one = [ ServerConstraintClause.AtLeast("n", 1) ]

              for value in [ "05"; "5.0"; " 5"; "+5"; "-0"; "five"; "9999999999999999999" ] do
                  Expect.equal
                      (decide one [ "n", JStr value ])
                      (Error(ServerConstraintDefect.OffList "n"))
                      $"'{value}' is not a canonical integer"
          }

          test "an absent argument passes vacuously" {
              let one = [ ServerConstraintClause.AtLeast("n", 1) ]
              Expect.isOk (decide one []) "nothing named"
              Expect.isOk (decide one [ "other", JInt 0 ]) "a different argument"
          }

          test "AtLeast and AtMost on one argument are an inclusive range" {
              let range =
                  [ ServerConstraintClause.AtLeast("n", 2)
                    ServerConstraintClause.AtMost("n", 4) ]

              for n, expected in [ 1, false; 2, true; 3, true; 4, true; 5, false ] do
                  Expect.equal (Result.isOk (decide range [ "n", JInt n ])) expected $"{n}"
          } ]

let private required =
    let heater =
        [ ServerConstraintClause.Required "minutes"
          ServerConstraintClause.AtLeast("minutes", 1) ]

    testList
        "Required — reproduced from the server placement's cases (Phase 2262)"
        [ test "an absent argument is refused, naming the declaration" {
              let given = [ ServerConstraintClause.Required "minutes" ]
              Expect.equal (decide given []) (Error(ServerConstraintDefect.Missing "minutes")) "nothing named"

              Expect.equal
                  (decide given [ "other", JInt 5 ])
                  (Error(ServerConstraintDefect.Missing "minutes"))
                  "a different argument is not this one"

              Expect.equal
                  (ArgumentPolicy.describe (ServerConstraintDefect.Missing "minutes"))
                  "argument-required:minutes"
                  "the token names the argument"
          }

          test "a present argument passes, whatever its value — presence is all it decides" {
              let given = [ ServerConstraintClause.Required "minutes" ]

              for value in [ JInt 0; JInt -5; JStr "five" ] do
                  Expect.isOk (decide given [ "minutes", value ]) $"%A{value}"
          }

          test "an argument the reader does not see is absent: a nested or boolean member is not given" {
              let given = [ ServerConstraintClause.Required "minutes" ]
              Expect.isError (decide given [ "minutes", JBool true ]) "a boolean is not read as an argument"

              Expect.isError
                  (decide given [ "minutes", JObj [ "value", JInt 5 ] ])
                  "a nested value is not read as an argument"
          }

          test "Required(minutes) and AtLeast(minutes, 1) refuse no minutes and 0, naming the clause" {
              Expect.equal (decide heater []) (Error(ServerConstraintDefect.Missing "minutes")) "no minutes"

              Expect.equal
                  (decide heater [ "minutes", JInt 0 ])
                  (Error(ServerConstraintDefect.OffList "minutes"))
                  "zero minutes"

              Expect.equal
                  (decide heater [ "minutes", JStr "ten" ])
                  (Error(ServerConstraintDefect.OffList "minutes"))
                  "a non-integer"

              Expect.isOk (decide heater [ "minutes", JInt 1 ]) "one minute"
              Expect.isOk (decide heater [ "minutes", JInt 30 ]) "thirty"
          }

          test "Required(count) and AtLeast(count, 2): the two tokens a planning refusal carries" {
              let counted =
                  [ ServerConstraintClause.Required "count"
                    ServerConstraintClause.AtLeast("count", 2) ]

              let token args =
                  decide counted args |> Result.mapError ArgumentPolicy.describe

              Expect.equal (token []) (Error "argument-required:count") "no count named"
              Expect.equal (token [ "count", JInt 1 ]) (Error "argument-not-allowed:count") "below the floor"
              Expect.equal (token [ "count", JInt 2 ]) (Ok()) "at the floor"
          } ]

let private lists =
    testList
        "the list clauses, the ceiling and the label, decided beside the clauses"
        [ test "an allow-list and a deny-list on one argument: a value either excludes is refused, in any order" {
              let allow = ServerConstraintClause.AllowList("target", [ "a"; "b" ])
              let deny = ServerConstraintClause.DenyList("target", [ "b" ])

              for clauses in [ [ allow; deny ]; [ deny; allow ] ] do
                  Expect.isOk (decide clauses [ "target", JStr "a" ]) "on the allow-list, off the deny-list"

                  Expect.equal
                      (decide clauses [ "target", JStr "b" ])
                      (Error(ServerConstraintDefect.OffList "target"))
                      "on both"

                  Expect.equal
                      (decide clauses [ "target", JStr "c" ])
                      (Error(ServerConstraintDefect.OffList "target"))
                      "on neither"

                  Expect.isOk (decide clauses []) "nothing named: vacuous"
          }

          test "a ceiling bounds the canonical bytes; declaration order decides which defect is reported first" {
              let args = [ "target", JStr "b" ]
              let size = System.Text.Encoding.UTF8.GetByteCount(ProgramWire.render (JObj args))
              Expect.isOk (decide [ ServerConstraintClause.Ceiling size ] args) "at the ceiling"

              let under = ServerConstraintClause.Ceiling(size - 1)
              let deny = ServerConstraintClause.DenyList("target", [ "b" ])

              Expect.equal
                  (decide [ under; deny ] args)
                  (Error(ServerConstraintDefect.OverCeiling(size - 1)))
                  "the ceiling, declared first"

              Expect.equal
                  (decide [ deny; under ] args)
                  (Error(ServerConstraintDefect.OffList "target"))
                  "the deny-list, declared first"
          }

          test "a label decides nothing, and no clause admits everything" {
              Expect.isOk (decide [ ServerConstraintClause.Label "egress" ] [ "n", JStr "anything" ]) "a label"
              Expect.isOk (decide [] [ "n", JStr "anything" ]) "unconstrained"
          }

          test "the host call's reading: string and integer members, nothing else, and nothing from a non-object" {
              Expect.equal
                  (ArgumentPolicy.ofObject (
                      JObj
                          [ "a", JStr "x"
                            "b", JInt 7
                            "c", JBool true
                            "d", JFloat 1.5
                            "e", JObj [ "f", JInt 1 ] ]
                  ))
                  [ "a", "x"; "b", "7" ]
                  "the flat string and integer members, in order"

              Expect.isEmpty (ArgumentPolicy.ofObject (JArr [ JInt 1 ])) "an array names nothing"
          } ]

let private windowed =
    testList
        "the windowed clauses reach the limiter the caller supplies, last and once"
        [ test "with no clock, a windowed clause refuses rather than admitting" {
              Expect.equal
                  (decide [ ServerConstraintClause.PerWindow(3, 60) ] []
                   |> Result.mapError ArgumentPolicy.describe)
                  (Error "limit-unjudgeable:no-clock")
                  "a bound nobody can judge admits nothing"
          }

          test "a window that is not positive is refused before any limiter is asked" {
              let mutable asked = false

              let limiter: WindowedLimiter =
                  fun _ _ _ ->
                      asked <- true
                      Ok()

              Expect.equal
                  (ArgumentPolicy.check limiter "c" [ ServerConstraintClause.Dwell 0 ] [] 0
                   |> Result.mapError ArgumentPolicy.describe)
                  (Error "limit-unjudgeable:window-not-positive")
                  "the declaration itself is unjudgeable"

              Expect.isFalse asked "the limiter was never asked"
          }

          test "the limiter is asked with the capability, the declared limit and the summed quantity" {
              let mutable seen = None

              let limiter: WindowedLimiter =
                  fun capability limit quantity ->
                      seen <- Some(capability, limit, quantity)
                      Ok()

              let clauses =
                  [ ServerConstraintClause.QuantityPerWindow("kwh", 100, 3600)
                    ServerConstraintClause.PerWindow(2, 60) ]

              Expect.isOk (ArgumentPolicy.check limiter "host:heat" clauses [ "kwh", "4"; "kwh", "6" ] 0) "admitted"

              Expect.equal
                  seen
                  (Some(
                      "host:heat",
                      { Count = Some(2, 60)
                        Quantity = Some("kwh", 100, 3600)
                        Dwell = None },
                      10L
                  ))
                  "one question, with the whole limit and the sum"
          }

          test "a stateless refusal is reported before the limiter could count an admission" {
              let mutable asked = false

              let limiter: WindowedLimiter =
                  fun _ _ _ ->
                      asked <- true
                      Ok()

              let clauses =
                  [ ServerConstraintClause.PerWindow(2, 60)
                    ServerConstraintClause.Required "minutes" ]

              Expect.equal
                  (ArgumentPolicy.check limiter "c" clauses [] 0)
                  (Error(ServerConstraintDefect.Missing "minutes"))
                  "refused by the stateless clause"

              Expect.isFalse asked "never admitted, so never counted"
          }

          test "a quantity that is not a non-negative canonical integer is refused under its argument" {
              let clauses = [ ServerConstraintClause.QuantityPerWindow("kwh", 100, 3600) ]

              for value in [ "-1"; "05"; "x" ] do
                  Expect.equal
                      (ArgumentPolicy.check (fun _ _ _ -> Ok()) "c" clauses [ "kwh", value ] 0)
                      (Error(ServerConstraintDefect.OffList "kwh"))
                      value
          } ]

let private placement =
    testList
        "the check needs no server package"
        [ test "Fuaran.Program.Bounded references no other Fuaran.Program package" {
              let referenced =
                  typeof<ServerConstraintClause>.Assembly.GetReferencedAssemblies()
                  |> Array.map (fun name -> name.Name)
                  |> Array.filter (fun name -> name.StartsWith "Fuaran.Program")

              Expect.isEmpty referenced "the check's package stands alone, so a leaf witness can reference only it"
          } ]

[<Tests>]
let tests =
    testList
        "the argument-policy check beside its clauses (Phase 2440, D59)"
        [ ceiling; floor; required; lists; windowed; placement ]
