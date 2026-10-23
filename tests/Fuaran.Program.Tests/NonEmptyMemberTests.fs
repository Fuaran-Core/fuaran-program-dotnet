module Fuaran.Program.Tests.NonEmptyMemberTests

// ─── the server-effect members the specification marks non-empty (Phase 2213, D51) ───
//
// PROGRAM_WIRE.md §5.1: `fn`, `name`, `channel`, `code` and `severity` MUST be
// non-empty. Until 0.12.0 the decoder held `fn` and the finding's two tokens to
// that and let a `RunQuery` with an empty `name` and a `Notify` with an empty
// `channel` decode. For each of the five members this pins:
//
//  1. the document with the member present and empty is refused, on
//     `missing-member`, and the refusal names the member and never the token;
//  2. the same document with the member non-empty round-trips, byte for byte;
//  3. the typed value with the member emptied still ENCODES, and what it encodes
//     to is refused — so a value round-trips through the encoder only when the
//     member is non-empty.

open Expecto
open Fuaran.Core
open Fuaran.Program.Bounded
open Fuaran.Program.Server
open Fuaran.Program.Tests.VerbDomain

type private VerbHandler = Handler<Nothing, FileOp>

let private handlerOf (effect: string) =
    """{"$type":"Handler","name":"h","stages":[{"$type":"Effect","effect":"""
    + effect
    + "}]}"

/// Each member, the effect document it sits in, and the same document with it
/// emptied.
let private members =
    [ "fn", """{"$type":"HostCall","args":{},"fn":"fetch-ledger"}""", """{"$type":"HostCall","args":{},"fn":""}"""
      "name",
      """{"$type":"RunQuery","name":"orders-slot","pipeline":[{"$type":"limit","n":5,"offset":0}],"source":{"ref":"orders","schema":[]}}""",
      """{"$type":"RunQuery","name":"","pipeline":[{"$type":"limit","n":5,"offset":0}],"source":{"ref":"orders","schema":[]}}"""
      "channel",
      """{"$type":"Notify","channel":"audit-feed","payload":{"event":"settled"}}""",
      """{"$type":"Notify","channel":"","payload":{"event":"settled"}}"""
      "code",
      """{"$type":"Report","code":"stale-order","message":"m","severity":"warning"}""",
      """{"$type":"Report","code":"","message":"m","severity":"warning"}"""
      "severity",
      """{"$type":"Report","code":"stale-order","message":"m","severity":"warning"}""",
      """{"$type":"Report","code":"stale-order","message":"m","severity":""}""" ]

/// The typed effect with the named member emptied.
let private emptied (memberName: string) (effect: ServerEffect<FileOp>) : ServerEffect<FileOp> =
    match memberName, effect with
    | "fn", ServerEffect.HostCall(_, args, into) -> ServerEffect.HostCall("", args, into)
    | "name", ServerEffect.RunQuery(_, source, pipeline) -> ServerEffect.RunQuery("", source, pipeline)
    | "channel", ServerEffect.Notify(_, payload) -> ServerEffect.Notify("", payload)
    | "code", ServerEffect.Report finding -> ServerEffect.Report { finding with Code = "" }
    | "severity", ServerEffect.Report finding -> ServerEffect.Report { finding with Severity = "" }
    | _ -> failtestf "no member %s on %A" memberName effect

let private refusalOf (document: string) =
    match HandlerWire.decodeHandler witness document with
    | Ok _ -> failtestf "decoded: %s" document
    | Error refusal -> refusal

[<Tests>]
let tests =
    testList
        "the server-effect members the specification marks non-empty (Phase 2213, D51)"
        [ for memberName, filled, empty in members do
              test $"an empty '{memberName}' is refused on missing-member, naming the member and not the token" {
                  let refusal = refusalOf (handlerOf empty)
                  Expect.equal refusal.Class RefusalClass.MissingMember "the class an absent member is refused on"

                  Expect.equal
                      refusal.Detail
                      $"member '{memberName}' is empty"
                      "one helper's refusal: the member named, nothing wire-carried echoed"
              }

              test $"a non-empty '{memberName}' round-trips, and the emptied value encodes to a refused document" {
                  let document = handlerOf filled

                  let decoded: VerbHandler =
                      match HandlerWire.decodeHandler witness document with
                      | Ok handler -> handler
                      | Error refusal -> failtestf "the non-empty document was refused: %A" refusal

                  Expect.equal (HandlerWire.encodeHandler witness decoded) (Ok document) "byte for byte"

                  let hollow =
                      { decoded with
                          Stages =
                              decoded.Stages
                              |> List.map (function
                                  | Effect effect -> Effect(emptied memberName effect)
                                  | stage -> stage) }

                  match HandlerWire.encodeHandler witness hollow with
                  | Error refusal -> failtestf "the encoder refused the typed value: %A" refusal
                  | Ok encoded ->
                      Expect.equal encoded (handlerOf empty) "the encoder writes the empty member as it is"

                      Expect.equal
                          (refusalOf encoded).Class
                          RefusalClass.MissingMember
                          "and the decoder refuses what it wrote"
              } ]
