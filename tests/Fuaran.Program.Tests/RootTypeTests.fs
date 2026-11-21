module Fuaran.Program.Tests.RootTypeTests

// ─── a document names its own type at the root (Phase 2449, D74) ─────────────
//
// PROGRAM_WIRE.md §2: a document's root `$type` names the document the reader
// was asked for, and is read before any other member. Until 0.17.0 the handler
// reader held its root to that and the outcome, invocation and logic-tree
// reference readers did not: each accepted a root naming another document, or
// none, which a second host refused. For each of the four documents this pins:
//
//  1. the document itself decodes;
//  2. the same members under a root naming each OTHER document are refused, on
//     `missing-member`, and the refusal does not echo the tag the document chose;
//  3. the same members with no `$type` are refused on the same class;
//  4. a whole document of another kind is refused on the same class — the root
//     is read before the member check, so the class does not depend on which
//     members the other document happens to carry.

open Expecto
open Fuaran.Program.Bounded
open Fuaran.Program.Server
open Fuaran.Program.Tests.VerbDomain

let private decodeAs (document: string) (bytes: string) : Result<unit, WireRefusal> =
    ProgramWire.parseDocument bytes
    |> Result.bind (fun value ->
        match document with
        | "handler" -> HandlerWire.decodeHandlerJson witness value |> Result.map ignore
        | "outcome" -> HandlerWire.decodeReportJson witness value |> Result.map ignore
        | "invocation" -> ProgramWire.decodeInvocation value |> Result.map ignore
        | "logic-tree-ref" -> ProgramWire.decodeLogicTreeRef value |> Result.map ignore
        | other -> failtestf "no reader for %s" other)

/// Each document, its root tag, its members after the tag, and the detail a
/// refusal carries.
let private documents =
    [ "handler", "Handler", "\"name\":\"h\",\"stages\":[]", "the document is not a handler document"
      "outcome",
      "HandlerReport",
      "\"committed\":true,\"diagnostics\":[],\"notifications\":[],\"patches\":[],\"performed\":[]",
      "the document is not an outcome document"
      "invocation",
      "Invocation",
      "\"endpoint\":\"/api/settle\",\"nodeId\":\"btn-settle\"",
      "the document is not an invocation document"
      "logic-tree-ref",
      "LogicTreeRef",
      "\"ref\":\"orders-logic\",\"slot\":\"fuaran.program/logic-tree\"",
      "the document is not a logic-tree reference" ]

let private article (document: string) =
    if document.StartsWith "outcome" || document.StartsWith "invocation" then
        "an"
    else
        "a"

let private typed (tag: string) (members: string) =
    "{\"$type\":\"" + tag + "\"," + members + "}"

let private refusedAsMissing (detail: string) (result: Result<unit, WireRefusal>) =
    match result with
    | Ok() -> failtest "decoded"
    | Error refusal ->
        Expect.equal refusal.Class RefusalClass.MissingMember "the class §2 names for a root of another kind"
        Expect.equal refusal.Detail detail "the expected document named, the chosen tag not echoed"

[<Tests>]
let tests =
    testList
        "a document names its own type at the root (Phase 2449, D74)"
        [ for document, tag, members, detail in documents do
              test $"{article document} {document} under its own root decodes" {
                  Expect.isOk (decodeAs document (typed tag members)) "the document itself"
              }

              for _, other, _, _ in documents |> List.filter (fun (_, t, _, _) -> t <> tag) do
                  test $"{article document} {document}'s members under a root naming {other} are refused" {
                      refusedAsMissing detail (decodeAs document (typed other members))
                  }

              test $"{article document} {document}'s members with no root type are refused" {
                  refusedAsMissing detail (decodeAs document ("{" + members + "}"))
              }

              for otherDocument, other, otherMembers, _ in documents |> List.filter (fun (_, t, _, _) -> t <> tag) do
                  test $"a whole {otherDocument} handed to the {document} reader is refused for the root" {
                      refusedAsMissing detail (decodeAs document (typed other otherMembers))
                  } ]
