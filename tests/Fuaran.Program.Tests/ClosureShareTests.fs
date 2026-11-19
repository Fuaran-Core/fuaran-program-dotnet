/// Phase 2446 (D71) — the closure share is one projection of the demanded
/// document.
///
/// How much of a program's behaviour stays inside the closed vocabularies, and
/// how much exits to a host, read off the document `Demanded.ofTree` and
/// `ServerDemanded` already produce: per tier, `Inside` and `Exits` as counts of
/// DISTINCT demands, and the share inside in basis points, rounded down. What is
/// pinned here:
///
///   * the definition — which member of each tier counts on which side, and
///     which counts on neither; distinct names; the two tiers never blended;
///   * the figure — rounded down, so one exit never reads as wholly closed, and
///     an empty tier reading 10000 with its counts saying it is empty;
///   * the walks — a tree with no exits, a tree whose only behaviour is a host
///     call, a server handler mixing compute stages and performed effects, and a
///     hand-authored tree with opaque handlers, each with its figure stated by
///     hand beside it;
///   * the document — version 15 carries `closure` on the client tier and on
///     every server tier, reads it back, and refuses a carried closure that its
///     lists do not project;
///   * the corpus — `conformance/demanded-closure-share.json` is what this file
///     emits, and every recorded reading is what the reader makes of it.
module Fuaran.Program.Tests.ClosureShareTests

open System
open System.IO
open System.Text.Json
open Expecto
open Fuaran.Core
open Fuaran.Program.Bounded
open Fuaran.Program.Server
open Fuaran.Program.Tests.ToyDomain

// ─── fixtures ────────────────────────────────────────────────────────────────

let private noCall = fun () -> ()

let private nodeOf (id: string) (handlers: (string * ToyAction) list) (children: ToyNode list) : ToyNode =
    { Id = id
      Label = Const(JStr id)
      Handlers = handlers
      Children = children }

let private put (key: string) : ToyAction = Put(key, Some(JStr "x"), None)

let private share (inside: int) (exits: int) : ClosureShare = { Inside = inside; Exits = exits }

/// A tree whose behaviour is all inside: two writes into two namespaces and a
/// beep. Client tier: `Sound`, `form`, `view` inside, nothing out — 3 / 0.
let private closedTree: ToyNode =
    nodeOf "root" [ "click", Seq [ put "form.name"; Beep 3 ] ] [ nodeOf "toggle" [ "press", put "view.mode" ] [] ]

/// A tree whose only behaviour is a host call: `Hush` names the `quiet` call on
/// the `Hush` channel. Client tier: 0 / 1.
let private hostCallTree: ToyNode = nodeOf "root" [ "click", Hush ] []

/// A tree whose only behaviour is a call action. At the client tier the
/// endpoint is a host call like any other: 0 / 1.
let private callTree: ToyNode =
    nodeOf "root" [ "submit", Ring("/handlers/settle", false, noCall) ] []

/// A handler mixing compute stages and performed effects. Its compute stages
/// join the CLIENT tier (`order` written, `Sound` caused); its effect stages the
/// SERVER tier: `ApplyOps`, `EmitPatch` and `Notify` inside, the `charge` host
/// function out — 3 / 1.
let private settle: Handler<ToyAction, ToyOp> =
    { Name = "settle"
      Stages =
        [ Compute(put "order.state")
          Compute(Beep 2)
          Effect(ServerEffect.ApplyOps [ Relabel("heater", "on") ])
          Effect(ServerEffect.EmitPatch [ Relabel("heater", "warm") ])
          Effect(ServerEffect.HostCall("charge", JObj [ "amount", JInt 2 ], None))
          Effect(ServerEffect.Notify("outbox", JStr "sent")) ] }

let private handlers: Map<string, Handler<ToyAction, ToyOp>> =
    Map.ofList [ "/handlers/settle", settle ]

/// The toy witness as a hand-authored tree reads it: a `change` handler is
/// closure-held, so the walk sees the event and no action for it — the node is
/// an OPAQUE HANDLER, the case a decoded tree never has.
let private undecodedWitness: FullWitness<ToyNode, ToyAction, ToyExpr, ToyStore, ToyOp, ToyEffect> =
    { witness with
        Dispatch =
            { witness.Dispatch with
                Handlers = fun n -> n.Handlers |> List.filter (fun (event, _) -> event <> "change") } }

/// Two nodes whose `change` handlers are closure-held, beside one write the
/// wire carried. Client tier: `form` inside; `picker` and `slider` out — 1 / 2.
let private undecodedTree: ToyNode =
    nodeOf
        "root"
        [ "click", put "form.name" ]
        [ nodeOf "picker" [ "change", put "form.choice" ] []
          nodeOf "slider" [ "change", put "form.level" ] [] ]

/// The toy witness with `Hush` declared an in-process escape (Phase 2130): an
/// act the wire DID carry whose behaviour lives in the host.
let private opaqueLeafWitness: FullWitness<ToyNode, ToyAction, ToyExpr, ToyStore, ToyOp, ToyEffect> =
    { witness with
        Dispatch =
            { witness.Dispatch with
                Action =
                    { witness.Dispatch.Action with
                        View =
                            fun action ->
                                match action with
                                | Hush -> ActionView.Leaf(LeafDeclaration.opaque "in-process" "Hush")
                                | other -> witness.Dispatch.Action.View other } } }

/// A beep beside an opaque leaf. Client tier: `Sound` inside, `Hush` out — 1 / 1.
let private opaqueLeafTree: ToyNode =
    nodeOf "root" [ "click", Seq [ Beep 1; Hush ] ] []

/// A tree that calls an endpoint no handler serves: a server walk that ran and
/// found nothing. Client tier 0 / 1; server tier 0 / 0.
let private tierlessTree: ToyNode =
    nodeOf "root" [ "submit", Ring("/handlers/nobody", false, noCall) ] []

let private closedDoc = Demanded.ofTree witness closedTree
let private hostCallDoc = Demanded.ofTree witness hostCallTree
let private callDoc = Demanded.ofTree witness callTree
let private mixedDoc = ServerDemanded.ofTreeAndHandlers witness handlers callTree
let private undecodedDoc = Demanded.ofTree undecodedWitness undecodedTree
let private opaqueLeafDoc = Demanded.ofTree opaqueLeafWitness opaqueLeafTree

let private tierlessDoc =
    ServerDemanded.ofTreeAndHandlers witness handlers tierlessTree

let private serverClosure (projection: DemandedProjection) : ClosureShare option =
    projection.Server |> Option.map _.Closure

// ─── the definition ──────────────────────────────────────────────────────────

[<Tests>]
let definition =
    testList
        "Phase 2446 - the closure share's definition"
        [ test "each client-tier member counts on its side, and the descriptive members on neither" {
              let one =
                  { Demanded.empty with
                      Effects = [ "Sound" ]
                      StateNamespaces =
                          [ { Namespace = "form"
                              Written = true
                              Read = false } ] }

              Expect.equal one.Closure (share 2 0) "an effect kind and a namespace are inside"

              let out =
                  { Demanded.empty with
                      HostCalls = [ { Channel = "Hush"; Name = "quiet" } ]
                      OpaqueHandlers = [ "picker" ]
                      OpaqueLeaves = [ { Reason = "in-process"; Name = "Hush" } ] }

              Expect.equal out.Closure (share 0 3) "a host call, an opaque handler and an opaque leaf exit"

              let descriptive =
                  { Demanded.empty with
                      Iterations = [ { Collection = "rows"; Ceiling = 4 } ]
                      Values = [ { Value = "total"; Targets = [ "sum" ] } ]
                      Quantities =
                          [ { Name = "beep-minutes"
                              Unit = minute
                              WorstCase = 3 } ] }

              Expect.equal descriptive.Closure (share 0 0) "an iteration, a value and a quantity are not behaviour"
          }

          test "each server-tier member counts on its side, and the descriptive members on neither" {
              let tier =
                  { Effects = [ "ApplyOps"; "HostCall"; "Notify" ]
                    Capabilities = [ "ApplyOps"; "Notify" ]
                    Functions =
                      [ { Function = "charge"
                          Capability = "host:charge" } ]
                    Channels = [ { Channel = "Notify"; Name = "outbox" } ]
                    Reach =
                      [ { Capability = "ApplyOps"
                          Argument = "target"
                          Name = "heater" } ]
                    Replay = []
                    Undo = []
                    Constraints = [] }

              Expect.equal tier.Closure (share 2 1) "the closed arms inside, the performer-backed function out"

              Expect.equal
                  { tier with
                      Effects = []
                      Channels = []
                      Reach = [] }
                      .Closure
                  (share 2 1)
                  "effects, channels and reach move nothing: the arms and the functions partition the tier"
          }

          test "names are counted once, so a document joined with itself counts what it did" {
              for projection in [ closedDoc; hostCallDoc; mixedDoc; undecodedDoc; opaqueLeafDoc ] do
                  let twice = Demanded.union [ projection; projection ]
                  Expect.equal twice.Closure projection.Closure "the client tier"
                  Expect.equal (serverClosure twice) (serverClosure projection) "the server tier"

              let duplicated =
                  { Demanded.empty with
                      Effects = [ "Sound"; "Sound" ]
                      StateNamespaces =
                          [ { Namespace = "form"
                              Written = true
                              Read = false }
                            { Namespace = "form"
                              Written = false
                              Read = true } ] }

              Expect.equal duplicated.Closure (share 2 0) "a namespace read and written is one namespace"

              let charge =
                  { Function = "charge"
                    Capability = "host:charge" }

              let tierTwice =
                  { Effects = []
                    Capabilities = [ "ApplyOps"; "ApplyOps" ]
                    Functions = [ charge; charge ]
                    Channels = []
                    Reach = []
                    Replay = []
                    Undo = []
                    Constraints = [] }

              Expect.equal tierTwice.Closure (share 1 1) "a server tier names each arm and function once"
          }

          test "the two tiers are never blended" {
              Expect.equal mixedDoc.Closure (share 2 1) "the client tier alone"
              Expect.equal (serverClosure mixedDoc) (Some(share 3 1)) "the server tier alone"
              Expect.isNone (serverClosure callDoc) "a document with no server walk has no server share"
          } ]

// ─── the figure ──────────────────────────────────────────────────────────────

[<Tests>]
let figure =
    testList
        "Phase 2446 - the closure share's figure"
        [ test "the share is in basis points, rounded down" {
              Expect.equal (share 2 1).BasisPoints 6666 "two thirds, rounded down"
              Expect.equal (share 1 2).BasisPoints 3333 "one third"
              Expect.equal (share 3 1).BasisPoints 7500 "exact"
              Expect.equal (share 0 1).BasisPoints 0 "all out"
              Expect.equal (share 1 0).BasisPoints 10000 "all in"
          }

          test "one exit never reads as wholly closed" {
              for inside in 0..60 do
                  for exits in 1..60 do
                      let points = (share inside exits).BasisPoints
                      Expect.isLessThan points 10000 (sprintf "%d inside, %d out" inside exits)
                      Expect.isGreaterThanOrEqual points 0 (sprintf "%d inside, %d out" inside exits)

              Expect.equal (share Int32.MaxValue 1).BasisPoints 9999 "and at the top of the range, without overflow"
          }

          test "a tier demanding nothing reads 10000, and its counts say it is empty" {
              Expect.equal Demanded.empty.Closure (share 0 0) "nothing counted"
              Expect.equal Demanded.empty.Closure.BasisPoints 10000 "nothing exits"
              Expect.equal (serverClosure tierlessDoc) (Some(share 0 0)) "a walk that ran and found nothing"
          } ]

// ─── the walks ───────────────────────────────────────────────────────────────

[<Tests>]
let walks =
    testList
        "Phase 2446 - the closure share over real walks"
        [ test "a tree with no exits is wholly inside" {
              Expect.equal closedDoc.Closure (share 3 0) "Sound, form, view"
              Expect.equal closedDoc.Closure.BasisPoints 10000 "the figure"
              Expect.isNone closedDoc.Server "no server walk"
          }

          test "a tree whose only behaviour is a host call is wholly out" {
              Expect.equal hostCallDoc.Closure (share 0 1) "the Hush call"
              Expect.equal hostCallDoc.Closure.BasisPoints 0 "the figure"
              Expect.equal callDoc.Closure (share 0 1) "a call action's endpoint, likewise"
          }

          test "a server handler mixing compute stages and performed effects, per tier" {
              Expect.equal mixedDoc.Closure (share 2 1) "Sound and order inside, the call out"
              Expect.equal mixedDoc.Closure.BasisPoints 6666 "the client figure"
              Expect.equal (serverClosure mixedDoc) (Some(share 3 1)) "ApplyOps, EmitPatch, Notify inside; charge out"
              Expect.equal (mixedDoc.Server |> Option.map _.Closure.BasisPoints) (Some 7500) "the server figure"
          }

          test "a hand-authored tree's opaque handlers exit" {
              Expect.equal undecodedDoc.OpaqueHandlers [ "picker"; "slider" ] "the walk saw two"
              Expect.equal undecodedDoc.Closure (share 1 2) "form inside, the two handlers out"
              Expect.equal undecodedDoc.Closure.BasisPoints 3333 "the figure"
          }

          test "an opaque leaf exits" {
              Expect.equal opaqueLeafDoc.Closure (share 1 1) "Sound inside, Hush out"
              Expect.equal opaqueLeafDoc.Closure.BasisPoints 5000 "the figure"
          } ]

// ─── the document ────────────────────────────────────────────────────────────

let private refusal (document: string) : (DemandedDefect * string) option =
    match Demanded.decode document with
    | Ok _ -> None
    | Error failure -> Some(failure.Defect, failure.Field)

/// `document` with `before` replaced by `after`, asserting the replacement
/// happened: an edit that matched nothing would leave a document that reads,
/// and a refusal test that passes on it would test nothing.
let private edited (before: string) (after: string) (document: string) : string =
    if not (document.Contains before) then
        failwithf "the edit does not apply: %s" before

    document.Replace(before, after)

let private clientClosureOf (projection: DemandedProjection) : string =
    let c = projection.Closure
    $"\"closure\":{{\"inside\":{c.Inside},\"exits\":{c.Exits},\"shareBasisPoints\":{c.BasisPoints}}},\"server\""

let private serverClosureOf (projection: DemandedProjection) : string =
    let c = projection.Server.Value.Closure
    $"\"constraints\":[],\"closure\":{{\"inside\":{c.Inside},\"exits\":{c.Exits},\"shareBasisPoints\":{c.BasisPoints}}}}}"

[<Tests>]
let document =
    testList
        "Phase 2446 - the demanded document carries the closure share at version 15"
        [ test "the version is 15" {
              Expect.equal Demanded.Version 15 "the version"
              Expect.equal Demanded.decodableVersions [ 15 ] "the only version read"
          }

          test "the client tier's share sits after quantities, the server tier's after constraints" {
              let bytes = Demanded.encode mixedDoc

              Expect.stringContains
                  bytes
                  "\"quantities\":[{\"name\":\"beep-minutes\",\"unit\":\"min\",\"worstCase\":2}],\"closure\":{\"inside\":2,\"exits\":1,\"shareBasisPoints\":6666},\"server\":{"
                  "the client tier's"

              Expect.stringContains
                  bytes
                  "\"constraints\":[],\"closure\":{\"inside\":3,\"exits\":1,\"shareBasisPoints\":7500}}}"
                  "the server tier's"
          }

          test "a document with no server walk carries the tree's share alone" {
              let bytes = Demanded.encode closedDoc

              Expect.stringContains
                  bytes
                  "\"closure\":{\"inside\":3,\"exits\":0,\"shareBasisPoints\":10000},\"server\":null}"
                  "one share, and the tier's absence beside it"
          }

          test "every walk's document reads back as itself, byte for byte" {
              for projection in
                  [ closedDoc
                    hostCallDoc
                    callDoc
                    mixedDoc
                    undecodedDoc
                    opaqueLeafDoc
                    tierlessDoc ] do
                  let bytes = Demanded.encode projection
                  Expect.equal (Demanded.decode bytes) (Ok projection) "decode inverts encode"

                  Expect.equal
                      (Demanded.decode bytes |> Result.map Demanded.encode)
                      (Ok bytes)
                      "and the bytes are stable"
          }

          test "a carried client share its lists do not project is refused at the member" {
              let bytes = Demanded.encode mixedDoc

              Expect.equal
                  (refusal (
                      edited
                          (clientClosureOf mixedDoc)
                          (clientClosureOf mixedDoc |> fun s -> s.Replace("\"inside\":2", "\"inside\":3"))
                          bytes
                  ))
                  (Some(DemandedDefect.NotCanonical, "closure"))
                  "an inside count"

              Expect.equal
                  (refusal (edited "\"shareBasisPoints\":6666" "\"shareBasisPoints\":6667" bytes))
                  (Some(DemandedDefect.NotCanonical, "closure"))
                  "a share rounded up"
          }

          test "a carried server share its lists do not project is refused at the member" {
              let bytes = Demanded.encode mixedDoc

              Expect.equal
                  (refusal (
                      edited
                          (serverClosureOf mixedDoc)
                          (serverClosureOf mixedDoc |> fun s -> s.Replace("\"exits\":1", "\"exits\":0"))
                          bytes
                  ))
                  (Some(DemandedDefect.NotCanonical, "server.closure"))
                  "an exits count"
          }

          test "a tier without its share is refused, never recounted" {
              let bytes = Demanded.encode mixedDoc

              Expect.equal
                  (refusal (edited ",\"closure\":{\"inside\":2,\"exits\":1,\"shareBasisPoints\":6666}" "" bytes))
                  (Some(DemandedDefect.MissingMember, "closure"))
                  "the client tier's"

              Expect.equal
                  (refusal (edited ",\"closure\":{\"inside\":3,\"exits\":1,\"shareBasisPoints\":7500}" "" bytes))
                  (Some(DemandedDefect.MissingMember, "server.closure"))
                  "the server tier's"

              Expect.equal
                  (refusal (
                      edited "\"closure\":{\"inside\":2,\"exits\":1,\"shareBasisPoints\":6666}" "\"closure\":null" bytes
                  ))
                  (Some(DemandedDefect.MissingMember, "closure"))
                  "a share spelled null is an absent one"
          }

          test "a share of the wrong shape is refused at the member that is wrong" {
              let bytes = Demanded.encode closedDoc
              let carried = "\"closure\":{\"inside\":3,\"exits\":0,\"shareBasisPoints\":10000}"

              Expect.equal
                  (refusal (edited carried "\"closure\":3" bytes))
                  (Some(DemandedDefect.WrongType, "closure"))
                  "not an object"

              Expect.equal
                  (refusal (
                      edited
                          carried
                          "\"closure\":{\"inside\":3,\"exits\":0,\"shareBasisPoints\":10000,\"blended\":1}"
                          bytes
                  ))
                  (Some(DemandedDefect.UndeclaredMember, "closure.blended"))
                  "a member the share does not declare"

              Expect.equal
                  (refusal (
                      edited carried "\"closure\":{\"inside\":\"3\",\"exits\":0,\"shareBasisPoints\":10000}" bytes
                  ))
                  (Some(DemandedDefect.WrongType, "closure.inside"))
                  "a count that is not an integer"
          } ]

// ─── the corpus ──────────────────────────────────────────────────────────────

/// The committed corpus, resolved from this source file.
let private corpusPath =
    Path.Combine(__SOURCE_DIRECTORY__, "..", "..", "conformance", "demanded-closure-share.json")
    |> Path.GetFullPath

/// A JSON string, escaped as the demanded family's corpus escapes one.
let private q = DemandedCorpusReadTests.q

let private renderShare (share: ClosureShare) : string =
    $"{{\"inside\":{share.Inside},\"exits\":{share.Exits},\"shareBasisPoints\":{share.BasisPoints}}}"

/// What the pinned reader makes of a document, as the corpus records it. A walk
/// that did not run is `"serverWalked":false` and no server share, never a null:
/// the demanded corpus's own rendering, for the readers it certifies.
let private renderRead (document: string) : string =
    match Demanded.decode document with
    | Ok projection ->
        let server =
            match projection.Server with
            | None -> "\"serverWalked\":false"
            | Some tier -> "\"serverWalked\":true,\"serverClosure\":" + renderShare tier.Closure

        "{\"verdict\":\"ok\",\"closure\":"
        + renderShare projection.Closure
        + ","
        + server
        + "}"
    | Error failure ->
        "{\"verdict\":\"refused\",\"defect\":"
        + q (sprintf "%A" failure.Defect)
        + ",\"field\":"
        + q failure.Field
        + "}"

/// The statement the ladder row cites, and the corpus carries at its head.
[<Literal>]
let Definition =
    "Per tier of the demanded document, over DISTINCT demands: the client tier counts its effect kinds and state namespaces inside, and its host calls (a call action's endpoint among them), opaque handlers and opaque leaves as exits; the server tier counts its closed arms' capabilities inside and its host functions as exits. The share is inside / (inside + exits) in basis points, rounded down, and 10000 for a tier demanding nothing. The two tiers are never added together, and a document with no server walk carries the client tier's share alone."

/// Every vector: its id, what it shows, and the document.
let private vectors () : (string * string * string) list =
    let mixed = Demanded.encode mixedDoc
    let closed = Demanded.encode closedDoc

    [ "no-exits",
      "A tree whose behaviour is all inside: two namespaces written and one effect kind caused. No server walk ran, so the client tier's share is the document's only one.",
      closed
      "host-call-only",
      "A tree whose only behaviour is a host call. Nothing inside, one exit.",
      Demanded.encode hostCallDoc
      "call-only",
      "A tree whose only behaviour is a call action. At the client tier its endpoint is an exit like any other host call.",
      Demanded.encode callDoc
      "server-mixed",
      "A server handler mixing compute stages and performed effects. Its compute stages join the client tier beside the tree's call; its closed arms are the server tier's inside, its host function the server tier's exit. Two shares, never blended.",
      mixed
      "undecoded-opaque-handlers",
      "A hand-authored tree whose closure-held handlers the walk can see only as events. Each such node is an exit.",
      Demanded.encode undecodedDoc
      "opaque-leaf",
      "A tree reaching a leaf that declares itself opaque: an act the wire carried whose behaviour lives in the host. It is an exit.",
      Demanded.encode opaqueLeafDoc
      "tier-walked-empty",
      "A tree calling an endpoint no handler serves. The server walk ran and found nothing: its share counts nothing and reads 10000, and the counts say it is empty.",
      Demanded.encode tierlessDoc
      "client-inside-disagrees",
      "A client share whose inside count its lists do not project. Refused: the share is derived, and a reader must be able to trust the carried figure without recounting.",
      mixed |> edited "\"closure\":{\"inside\":2," "\"closure\":{\"inside\":3,"
      "client-share-rounded-up",
      "A client share rounded up. Refused: the figure is rounded down, so one exit never reads as more closed than it is.",
      mixed |> edited "\"shareBasisPoints\":6666" "\"shareBasisPoints\":6667"
      "server-exits-disagrees",
      "A server share whose exits count its lists do not project.",
      mixed
      |> edited "\"closure\":{\"inside\":3,\"exits\":1," "\"closure\":{\"inside\":3,\"exits\":0,"
      "missing-client-closure",
      "A document without the client tier's share. Refused, never recounted: an absent share says the producer predates it.",
      closed
      |> edited ",\"closure\":{\"inside\":3,\"exits\":0,\"shareBasisPoints\":10000}" ""
      "missing-server-closure",
      "A server tier without its share.",
      mixed
      |> edited ",\"closure\":{\"inside\":3,\"exits\":1,\"shareBasisPoints\":7500}" ""
      "undeclared-closure-member",
      "A share carrying a member it does not declare: there is no blended figure.",
      closed
      |> edited "\"shareBasisPoints\":10000}" "\"shareBasisPoints\":10000,\"blended\":10000}" ]

/// The corpus as this file emits it.
let emitCorpus () : string =
    let lines =
        vectors ()
        |> List.map (fun (id, description, document) ->
            "    {\"id\":"
            + q id
            + ",\"description\":"
            + q description
            + ",\"document\":"
            + q document
            + ",\"read\":"
            + renderRead document
            + "}")

    "{\n"
    + "  \"corpus\": \"demanded-closure-share\",\n"
    + "  \"documentKind\": \"demanded\",\n"
    + $"  \"decodableVersions\": [{Demanded.Version}],\n"
    + "  \"definition\": "
    + q Definition
    + ",\n"
    + "  \"generator\": \"tests/Fuaran.Program.Tests/ClosureShareTests.fs (emitCorpus)\",\n"
    + "  \"vectors\": [\n"
    + String.concat ",\n" lines
    + "\n  ]\n}\n"

[<Tests>]
let corpus =
    testList
        "Phase 2446 - the closure-share corpus"
        [ test "the committed corpus is what this file emits" {
              let committed = File.ReadAllText(corpusPath).Replace("\r\n", "\n")
              let emitted = emitCorpus ()

              if committed <> emitted then
                  let derived = Path.Combine(Path.GetTempPath(), "demanded-closure-share.json")
                  File.WriteAllText(derived, emitted)
                  failtestf "the committed corpus differs from the emission; the emission is at %s" derived
          }

          test "every recorded reading is what the reader makes of its document" {
              use doc = JsonDocument.Parse(File.ReadAllText corpusPath)
              let root = doc.RootElement
              Expect.equal (root.GetProperty("corpus").GetString()) "demanded-closure-share" "the corpus name"
              Expect.equal (root.GetProperty("documentKind").GetString()) Demanded.Kind "the document kind"

              Expect.equal
                  [ for v in root.GetProperty("decodableVersions").EnumerateArray() -> v.GetInt32() ]
                  Demanded.decodableVersions
                  "the versions the reader reads"

              Expect.equal (root.GetProperty("definition").GetString()) Definition "the statement the ladder cites"

              let vectors = [ for v in root.GetProperty("vectors").EnumerateArray() -> v ]
              Expect.isNonEmpty vectors "vectors"

              for v in vectors do
                  let id = v.GetProperty("id").GetString()
                  let derived = renderRead (v.GetProperty("document").GetString())
                  Expect.equal derived (v.GetProperty("read").GetRawText()) id
          }

          test "the corpus carries the four required cases, read ok, and both tiers" {
              use doc = JsonDocument.Parse(File.ReadAllText corpusPath)

              let reads =
                  [ for v in doc.RootElement.GetProperty("vectors").EnumerateArray() ->
                        v.GetProperty("id").GetString(), v.GetProperty("read") ]
                  |> Map.ofList

              for id in [ "no-exits"; "host-call-only"; "server-mixed"; "undecoded-opaque-handlers" ] do
                  Expect.equal (reads[id].GetProperty("verdict").GetString()) "ok" id

              Expect.isTrue
                  (reads["server-mixed"].GetProperty("serverWalked").GetBoolean())
                  "a server tier is certified"

              Expect.isFalse (reads["no-exits"].GetProperty("serverWalked").GetBoolean()) "and a document without one"
          }

          // The ladder's row and the corpus state ONE definition: the row's
          // claim is the corpus's statement, character for character, and its
          // evidence names this file and the corpus.
          test "the proof ladder's row states the corpus's definition" {
              let ladder =
                  Path.Combine(__SOURCE_DIRECTORY__, "..", "..", "proofs.json")
                  |> File.ReadAllText

              use doc = JsonDocument.Parse ladder

              let row =
                  doc.RootElement.GetProperty("claims").EnumerateArray()
                  |> Seq.tryFind (fun c -> c.GetProperty("id").GetString() = "closure-share-definition")

              match row with
              | None -> failtest "proofs.json has no closure-share-definition row"
              | Some row ->
                  Expect.equal (row.GetProperty("level").GetString()) "tested" "a tested row"
                  Expect.equal (row.GetProperty("claim").GetString()) Definition "its statement is the definition"
                  let evidence = row.GetProperty("evidence")

                  Expect.equal
                      (evidence.GetProperty("host").GetString())
                      "tests/Fuaran.Program.Tests/ClosureShareTests.fs"
                      "hosted here"

                  Expect.equal
                      (evidence.GetProperty("artifact").GetString())
                      "conformance/demanded-closure-share.json"
                      "its family is the corpus"
          }

          // The demanded family's documents were re-cut at version 15 by hand,
          // its emitter living in the UI tier's repository. Every document that
          // reads is held to the encoder's own bytes, so a share in the wrong
          // place or with the wrong count cannot sit in the copy unnoticed: the
          // reader checks the counts, and only this checks the member's place.
          test "every document the demanded family reads is the encoder's own bytes" {
              let demandedPath =
                  Path.Combine(__SOURCE_DIRECTORY__, "..", "..", "conformance", "demanded-effect-projection.json")

              use doc = JsonDocument.Parse(File.ReadAllText demandedPath)

              let read =
                  [ for v in doc.RootElement.GetProperty("vectors").EnumerateArray() ->
                        v.GetProperty("id").GetString(), v.GetProperty("document").GetString() ]
                  |> List.choose (fun (id, document) ->
                      match Demanded.decode document with
                      | Ok projection -> Some(id, document, Demanded.encode projection)
                      | Error _ -> None)

              Expect.isNonEmpty read "some documents read"

              for id, document, reencoded in read do
                  Expect.equal reencoded document id
          } ]
