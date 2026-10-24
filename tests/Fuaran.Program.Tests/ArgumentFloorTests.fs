module Fuaran.Program.Tests.ArgumentFloorTests

// ─── A floor and an opt-in Required clause (Phase 2262, D55) ─────────
//
// `AtMost` gave a number a ceiling and nothing gave it a floor, and an
// argument the effect never named passed every clause vacuously — so a device
// read "no duration given" as "no limit". `AtLeast(argument, limit)` is
// `AtMost`'s reading with the other end bounded; `Required(argument)` is the
// one clause that is not vacuous over an absent argument, and it decides
// presence alone.

open Expecto
open Fuaran.Core
open Fuaran.Compute
open Fuaran.Program.Bounded
open Fuaran.Program.Server
open Fuaran.Program.Tests.VerbDomain

let private bounded (clauses: ServerConstraintClause list) (capability: string) : ServerEffectRegistry =
    ServerEffectRegistry.permissive ServerEffectRegistry.denyAll
    |> ServerEffectRegistry.constrain capability clauses

let private checkArgs (registry: ServerEffectRegistry) (args: (string * JVal) list) =
    ServerArgumentPolicy.check witness.State registry (ServerEffect.HostCall("heat", JObj args, None))

let private runIn (registry: ServerEffectRegistry) (world: World) (handler: Handler<Nothing, FileOp>) =
    Handler.runWith
        witness
        registry
        (OpPerformance.performedWithDetail (world.Performer None))
        DataFrame.noResolve
        "verb"
        handler
        { Tree = { Files = world.Files; Published = [] }
          Bindings = () }

let private handlerOf (ops: FileOp list) : Handler<Nothing, FileOp> =
    { Name = "poll"
      Stages = [ Effect(ServerEffect.ApplyOps ops) ] }

/// The acceptance's declaration: a duration that must be given and must be at
/// least one.
let private heater =
    bounded
        [ ServerConstraintClause.Required "minutes"
          ServerConstraintClause.AtLeast("minutes", 1) ]
        "host:heat"

let private floor =
    testList
        "AtLeast — AtMost's reading with the other end bounded"
        [ test "present arguments: at and above the floor admit, below it refuses under the argument" {
              let one = bounded [ ServerConstraintClause.AtLeast("n", 1) ] "host:heat"

              for args, expected in
                  [ [ "n", JInt 1 ], true
                    [ "n", JInt 90 ], true
                    [ "n", JInt 0 ], false
                    [ "n", JInt -1 ], false
                    [ "n", JStr "1" ], true
                    [ "n", JStr "0" ], false ] do
                  let verdict = checkArgs one args
                  Expect.equal (Result.isOk verdict) expected $"%A{args}"

                  if not expected then
                      Expect.equal verdict (Error(ServerConstraintDefect.OffList "n")) "the allow-list's token"
          }

          test "a non-integer value is refused, in every spelling AtMost refuses" {
              let one = bounded [ ServerConstraintClause.AtLeast("n", 1) ] "host:heat"

              for value in [ "05"; "5.0"; " 5"; "+5"; "-0"; "five"; "9999999999999999999" ] do
                  Expect.equal
                      (checkArgs one [ "n", JStr value ])
                      (Error(ServerConstraintDefect.OffList "n"))
                      $"'{value}' is not a canonical integer"
          }

          test "an absent argument passes vacuously — the default stays as it was" {
              let one = bounded [ ServerConstraintClause.AtLeast("n", 1) ] "host:heat"
              Expect.isOk (checkArgs one []) "nothing named"
              Expect.isOk (checkArgs one [ "other", JInt 0 ]) "a different argument"
          }

          test "AtLeast and AtMost on one argument are an inclusive range" {
              let range =
                  bounded
                      [ ServerConstraintClause.AtLeast("n", 2)
                        ServerConstraintClause.AtMost("n", 4) ]
                      "host:heat"

              for n, expected in [ 1, false; 2, true; 3, true; 4, true; 5, false ] do
                  Expect.equal (Result.isOk (checkArgs range [ "n", JInt n ])) expected $"{n}"
          } ]

let private required =
    testList
        "Required — the one clause not vacuous over an absent argument"
        [ test "an absent argument is refused, naming the declaration" {
              let given = bounded [ ServerConstraintClause.Required "minutes" ] "host:heat"
              Expect.equal (checkArgs given []) (Error(ServerConstraintDefect.Missing "minutes")) "nothing named"

              Expect.equal
                  (checkArgs given [ "other", JInt 5 ])
                  (Error(ServerConstraintDefect.Missing "minutes"))
                  "a different argument is not this one"

              Expect.equal
                  (ServerArgumentPolicy.describe (ServerConstraintDefect.Missing "minutes"))
                  "argument-required:minutes"
                  "the token names the argument"
          }

          test "a present argument passes, whatever its value — presence is all it decides" {
              let given = bounded [ ServerConstraintClause.Required "minutes" ] "host:heat"

              for value in [ JInt 0; JInt -5; JStr "five" ] do
                  Expect.isOk (checkArgs given [ "minutes", value ]) $"%A{value}"
          }

          test "an argument the reader does not see is absent: a nested or boolean member is not given" {
              let given = bounded [ ServerConstraintClause.Required "minutes" ] "host:heat"

              Expect.isError (checkArgs given [ "minutes", JBool true ]) "a boolean is not read as an argument"

              Expect.isError
                  (checkArgs given [ "minutes", JObj [ "value", JInt 5 ] ])
                  "a nested value is not read as an argument"
          }

          test "the acceptance: Required(minutes) and AtLeast(minutes, 1) refuse no minutes and 0, naming the clause" {
              Expect.equal (checkArgs heater []) (Error(ServerConstraintDefect.Missing "minutes")) "no minutes"

              Expect.equal
                  (checkArgs heater [ "minutes", JInt 0 ])
                  (Error(ServerConstraintDefect.OffList "minutes"))
                  "zero minutes"

              Expect.equal
                  (checkArgs heater [ "minutes", JStr "ten" ])
                  (Error(ServerConstraintDefect.OffList "minutes"))
                  "a non-integer"

              Expect.isOk (checkArgs heater [ "minutes", JInt 1 ]) "one minute"
              Expect.isOk (checkArgs heater [ "minutes", JInt 30 ]) "thirty"
          }

          test "a handler run refuses while planning, before anything performs" {
              let registry =
                  bounded
                      [ ServerConstraintClause.Required "count"
                        ServerConstraintClause.AtLeast("count", 2) ]
                      "ApplyOps"

              let world = World()
              let absent = runIn registry world (handlerOf [ Publish "origin" ])
              Expect.isFalse absent.Committed "no count named"
              Expect.isEmpty world.Invocations "the performer was never asked"

              Expect.equal
                  absent.Diagnostics
                  [ ServerDiagnostic.Failed("ApplyOps", "argument-required:count") ]
                  "refused naming the Required clause's argument"

              let world' = World()
              let low = runIn registry world' (handlerOf [ Times(1, [ Publish "origin" ]) ])
              Expect.isFalse low.Committed "one is below the floor"
              Expect.isEmpty world'.Invocations "the performer was never asked"

              Expect.equal
                  low.Diagnostics
                  [ ServerDiagnostic.Failed("ApplyOps", "argument-not-allowed:count") ]
                  "refused under the floor's token"

              let world'' = World()
              let admitted = runIn registry world'' (handlerOf [ Times(2, [ Publish "origin" ]) ])
              Expect.isTrue admitted.Committed "two is at the floor"
              Expect.equal world''.Published.Length 2 "and both ran"
          } ]

let private document =
    testList
        "the demanded document carries both clauses"
        [ test "both ride the document at version 14 and read back clause for clause" {
              let projection =
                  ServerDemanded.ofHandler witness (handlerOf [ Times(3, [ Publish "origin" ]) ])
                  |> ServerDemanded.withConstraints (
                      bounded
                          [ ServerConstraintClause.Required "count"
                            ServerConstraintClause.AtLeast("count", 1) ]
                          "ApplyOps"
                  )

              let encoded = Demanded.encode projection
              Expect.equal Demanded.Version 14 "the version the two clauses moved it to"
              Expect.stringContains encoded "\"version\":14" "carried in the document"

              Expect.stringContains
                  encoded
                  "[{\"clause\":\"atLeast\",\"argument\":\"count\",\"limit\":1},{\"clause\":\"required\",\"argument\":\"count\"}]"
                  "both clauses, in the canonical clause order rather than the declared one"

              match Demanded.decode encoded with
              | Ok read -> Expect.equal read projection "read back to the same projection"
              | Error failure -> failtestf "the document does not read back: %A" failure
          }

          test "a malformed clause is refused at its member" {
              let projection =
                  ServerDemanded.ofHandler witness (handlerOf [ Times(3, [ Publish "origin" ]) ])
                  |> ServerDemanded.withConstraints (
                      bounded
                          [ ServerConstraintClause.Required "count"
                            ServerConstraintClause.AtLeast("count", 1) ]
                          "ApplyOps"
                  )

              let encoded = Demanded.encode projection

              let stringLimit = encoded.Replace("\"limit\":1}", "\"limit\":\"1\"}")

              match Demanded.decode stringLimit with
              | Ok _ -> failtest "a floor that is not an integer was read"
              | Error failure -> Expect.stringContains failure.Field "limit" "refused at the limit"

              let strayMember =
                  encoded.Replace(
                      "{\"clause\":\"required\",\"argument\":\"count\"}",
                      "{\"clause\":\"required\",\"argument\":\"count\",\"limit\":1}"
                  )

              match Demanded.decode strayMember with
              | Ok _ -> failtest "a required clause carrying a limit was read"
              | Error failure -> Expect.stringContains failure.Field "limit" "refused at the undeclared member"
          } ]

[<Tests>]
let tests =
    testList "a floor and an opt-in Required clause (Phase 2262, D55)" [ floor; required; document ]
