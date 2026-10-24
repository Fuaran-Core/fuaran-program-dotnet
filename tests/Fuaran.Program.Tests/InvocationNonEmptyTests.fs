module Fuaran.Program.Tests.InvocationNonEmptyTests

// ─── the invocation members the specification marks non-empty (Phase 2436, D53) ───
//
// PROGRAM_WIRE.md §8.3: `endpoint` and `nodeId` are "string, non-empty". Until
// 0.12.0 the invocation decoder read both with a bare string check, so an
// invocation naming no entry point, or no originating node, decoded. For each
// of the two members this pins:
//
//  1. the document with the member present and empty is refused, on
//     `missing-member`, and the refusal names the member and never the token —
//     the same class and detail the handler decoder gives `fn`, `name` and
//     `channel` (Phase 2213), because it is the same helper;
//  2. the same document with the member non-empty round-trips, byte for byte;
//  3. the typed record with the member emptied still ENCODES, and what it
//     encodes to is refused — so a record round-trips through the encoder only
//     when the member is non-empty.
//
// The go-red check is the first test: against the 0.11 decoder each emptied
// document decoded, which is exactly the failure it reports.

open Expecto
open Fuaran.Program.Bounded

/// Each member, the invocation it sits in, and the same invocation with it
/// emptied. The key rides along on one of them so the empty-member check is
/// shown to come before the key's own.
let private members =
    [ "endpoint",
      """{"$type":"Invocation","endpoint":"/api/settle","idempotencyKey":"k-1","nodeId":"btn-settle"}""",
      """{"$type":"Invocation","endpoint":"","idempotencyKey":"k-1","nodeId":"btn-settle"}"""
      "nodeId",
      """{"$type":"Invocation","endpoint":"/api/refresh","nodeId":"btn-refresh"}""",
      """{"$type":"Invocation","endpoint":"/api/refresh","nodeId":""}""" ]

let private decode (document: string) =
    ProgramWire.parseDocument document |> Result.bind ProgramWire.decodeInvocation

let private refusalOf (document: string) =
    match decode document with
    | Ok record -> failtestf "decoded %A from %s" record document
    | Error refusal -> refusal

let private emptied (memberName: string) (record: InvocationRecord) : InvocationRecord =
    match memberName with
    | "endpoint" -> { record with Endpoint = "" }
    | "nodeId" -> { record with NodeId = "" }
    | other -> failtestf "no member %s on an invocation" other

[<Tests>]
let tests =
    testList
        "the invocation members the specification marks non-empty (Phase 2436, D53)"
        [ for memberName, filled, empty in members do
              test $"an empty '{memberName}' is refused on missing-member, naming the member and not the token" {
                  let refusal = refusalOf empty
                  Expect.equal refusal.Class RefusalClass.MissingMember "the class an absent member is refused on"

                  Expect.equal
                      refusal.Detail
                      $"member '{memberName}' is empty"
                      "the handler decoder's refusal: the member named, nothing wire-carried echoed"
              }

              test $"a non-empty '{memberName}' round-trips, and the emptied record encodes to a refused document" {
                  let record =
                      match decode filled with
                      | Ok record -> record
                      | Error refusal -> failtestf "the non-empty invocation was refused: %A" refusal

                  Expect.equal (ProgramWire.render (ProgramWire.encodeInvocation record)) filled "byte for byte"

                  let encoded =
                      ProgramWire.render (ProgramWire.encodeInvocation (emptied memberName record))

                  Expect.equal encoded empty "the encoder writes the empty member as it is"

                  Expect.equal
                      (refusalOf encoded).Class
                      RefusalClass.MissingMember
                      "and the decoder refuses what it wrote"
              }

          test "an absent member is still refused as absent, not as empty" {
              let refusal = refusalOf """{"$type":"Invocation","nodeId":"btn-settle"}"""

              Expect.equal refusal.Class RefusalClass.MissingMember "missing-member"
              Expect.equal refusal.Detail "required member 'endpoint' is absent" "absence keeps its own detail"
          } ]
