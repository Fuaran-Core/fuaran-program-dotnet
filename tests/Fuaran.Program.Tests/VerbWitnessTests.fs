/// The second witness, exercised against the four findings Phase 1967
/// answered (`DECISIONS.md` D19), one adversary per finding:
///
///   W3/W4  an off-list publish target is refused BEFORE anything performs,
///          and the demanded document names the paths and the target;
///   F1     a guard that does not hold halts the handler with NOTHING
///          performed;
///   F2     a part-way performance failure is reported with the prefix that
///          ran and the position it failed at;
///   W5     a typed refusal crosses the op channel as text and parses back.
///
/// Since Phase 1974 (`DECISIONS.md` D20) the verb fills the STATE AXIS ONLY,
/// and every test here runs it so: its handlers carry no compute stage (its
/// action type has no values), its guards are op-channel guards resolved
/// against the plan, and its performer is handed the planned state.
///
/// This project references the three core packages and no UI-tier package,
/// so the verb is the whole domain here, as the toy is beside it.
module Fuaran.Program.Tests.VerbWitnessTests

open Expecto
open Fuaran.Core
open Fuaran.Compute
open Fuaran.Program.Bounded
open Fuaran.Program.Server
open Fuaran.Program.Tests.VerbDomain

let private empty: FileMap = { Files = Map.empty; Published = [] }

/// A handler under a witness that fills no dispatch axis: effect stages only.
type private VerbHandler = Handler<Nothing, FileOp>

/// The verb: check the note exists, read it, write the archive copy, delete
/// the old one, check it is gone, publish.
let private archive: VerbHandler =
    { Name = "archive"
      Stages =
        [ Effect(ServerEffect.ApplyOps [ Check(Exists "notes/x.md"); Read "notes/x.md" ])
          Effect(ServerEffect.ApplyOps [ Write("notes/archive/x.md", "archived"); Delete "notes/x.md" ])
          Effect(ServerEffect.ApplyOps [ Check(Missing "notes/x.md"); Publish "origin" ]) ] }

/// A registry admitting every capability, with the verb's own policy: ops
/// may reach the notes store, locally, and publish to `origin` and nowhere
/// else — the destination CLASS bound beside the named target (W4).
let private registry: ServerEffectRegistry =
    ServerEffectRegistry.permissive ServerEffectRegistry.denyAll
    |> ServerEffectRegistry.constrain
        "ApplyOps"
        [ ServerConstraintClause.AllowList("path", [ "notes/x.md"; "notes/archive/x.md" ])
          ServerConstraintClause.AllowList("target", [ "origin" ])
          ServerConstraintClause.AllowList(ServerArgumentPolicy.DestinationArgument, [ "local"; "origin" ]) ]

let private seeded () =
    let world = World()
    world.Seed("notes/x.md", "live")
    world

let private runIn
    (registry: ServerEffectRegistry)
    (world: World)
    (failAt: int option)
    (handler: VerbHandler)
    (tree: FileMap)
    : HandlerOutcome<FileMap, unit, FileOp, Nothing> =
    Handler.runWith
        witness
        registry
        (OpPerformance.performedWithDetail (world.Performer failAt))
        DataFrame.noResolve
        "verb"
        handler
        { Tree = tree; Bindings = () }

let private run (world: World) (failAt: int option) (handler: VerbHandler) =
    runIn registry world failAt handler { empty with Files = world.Files }

/// Phase 1981: the verb under an op performance the test chooses — a checked
/// performer, or the adversary — over the same registry and witness.
let private runPerforming (world: World) (performance: OpPerformance<FileMap, FileOp>) (handler: VerbHandler) =
    Handler.runWith
        witness
        registry
        performance
        DataFrame.noResolve
        "verb"
        handler
        { Tree = { empty with Files = world.Files }
          Bindings = () }

// ─── Phase 1976: the two flow shapes on the op axis ─────────────────────────

/// The archive policy, widened for the flow tests: the marker the false arm
/// writes, and a CEILING on a repeat's count — the verb names the count as an
/// argument of the repeat's reach, so an allow-list bounds how many times a
/// body may run, and an over-bound repeat is refused before anything performs.
let private flowRegistry: ServerEffectRegistry =
    ServerEffectRegistry.permissive ServerEffectRegistry.denyAll
    |> ServerEffectRegistry.constrain
        "ApplyOps"
        [ ServerConstraintClause.AllowList("path", [ "notes/x.md"; "notes/archive/x.md"; "notes/created.marker" ])
          ServerConstraintClause.AllowList("target", [ "origin" ])
          ServerConstraintClause.AllowList(ServerArgumentPolicy.DestinationArgument, [ "local"; "origin" ])
          ServerConstraintClause.AllowList("count", [ "1"; "2"; "3" ]) ]

/// The verb's two-arm construct, IN Program: migrate the note if it is there,
/// create it (and leave a marker) if not, then publish. The exit assertion —
/// no marker — holds after the true arm and fails after the false arm, which
/// is the Janus discipline the inverse rests on.
let private migrate: VerbHandler =
    { Name = "migrate"
      Stages =
        [ Effect(
              ServerEffect.ApplyOps
                  [ Branch(
                        Exists "notes/x.md",
                        [ Write("notes/x.md", "migrated") ],
                        [ Write("notes/x.md", "created"); Write("notes/created.marker", "") ],
                        Some(Missing "notes/created.marker")
                    )
                    Publish "origin" ]
          ) ] }

let private flowRun (world: World) (handler: VerbHandler) =
    runIn flowRegistry world None handler { empty with Files = world.Files }

[<Tests>]
let tests =
    testList
        "Phase 1967 — the second witness: a verb over a file map"
        [ test "the verb runs: guards that hold, a plan applied, the plan performed after it commits" {
              let world = seeded ()
              let outcome = run world None archive

              Expect.isTrue outcome.Committed "the handler commits"

              Expect.equal
                  outcome.Performed
                  [ "ApplyOps"; "ApplyOps"; "ApplyOps"; "ApplyOps" ]
                  "four edits performed, each its own staged call, in plan order — the two checks are guards and never performed"

              Expect.equal
                  (world.Files |> Map.toList)
                  [ "notes/archive/x.md", "archived" ]
                  "the world was written and the old note deleted — AFTER the plan committed"

              Expect.equal world.Published [ "origin" ] "and published"
              Expect.equal outcome.Store.Tree.Published [ "origin" ] "the committed plan agrees with the world"

              Expect.isFalse
                  (world.Invocations
                   |> List.exists (fun op -> op.Contains "Exists" || op.Contains "Missing"))
                  "no guard reached the performer"
          }

          // ── W3 / W4: the envelope says what the ops reach, and the policy binds it ──

          test "the demanded document names the paths and the target the verb's ops reach — and is pinned" {
              let projection = ServerDemanded.ofHandler witness archive

              let tier =
                  match projection.Server with
                  | Some tier -> tier
                  | None -> failtest "the walk ran, so the document must carry a server tier"

              Expect.equal
                  (tier.Reach |> List.map (fun r -> r.Capability, r.Argument, r.Name))
                  [ "ApplyOps", "destination", "local"
                    "ApplyOps", "destination", "origin"
                    "ApplyOps", "path", "notes/archive/x.md"
                    "ApplyOps", "path", "notes/x.md"
                    "ApplyOps", "target", "origin" ]
                  "every path, the target, and the two destination classes — distinct and sorted; the guards' paths are among them"

              // The document's bytes, pinned: this projection is this
              // repository's own artefact (docs/generic-tier.md §6), and the
              // reach is what version 5 added to it and the empty undo posture
              // what version 6 added (Phase 1977). A state-only verb reads
              // no state namespace — it has no binding store (Phase 1974).
              Expect.equal
                  (Demanded.encode projection)
                  ($"{{\"kind\":\"demanded\",\"version\":{Demanded.Version},\"effects\":[],\"hostCalls\":[],"
                   + "\"stateNamespaces\":[],"
                   + "\"opaqueHandlers\":[],\"iterations\":[],\"opaqueLeaves\":[],\"values\":[],\"quantities\":[],\"closure\":{\"inside\":0,\"exits\":0,\"shareBasisPoints\":10000},\"server\":{\"effects\":[\"ApplyOps\"],\"capabilities\":[\"ApplyOps\"],"
                   + "\"functions\":[],\"channels\":[],"
                   + "\"reach\":[{\"capability\":\"ApplyOps\",\"argument\":\"destination\",\"name\":\"local\"},"
                   + "{\"capability\":\"ApplyOps\",\"argument\":\"destination\",\"name\":\"origin\"},"
                   + "{\"capability\":\"ApplyOps\",\"argument\":\"path\",\"name\":\"notes/archive/x.md\"},"
                   + "{\"capability\":\"ApplyOps\",\"argument\":\"path\",\"name\":\"notes/x.md\"},"
                   + "{\"capability\":\"ApplyOps\",\"argument\":\"target\",\"name\":\"origin\"}],"
                   + "\"replay\":[],\"undo\":[],\"constraints\":[],\"closure\":{\"inside\":1,\"exits\":0,\"shareBasisPoints\":10000}}}")
                  "the document's bytes"

              // And read back: the reach survives the round trip, so a reader
              // holding only the document sees what the handler holds.
              match Demanded.decode (Demanded.encode projection) with
              | Ok read -> Expect.equal read projection "the document reads back as the projection"
              | Error failure -> failtestf "the document does not read back: %A" failure

              // The policy travels beside the reach it bounds.
              let withPolicy = ServerDemanded.withConstraints registry projection

              Expect.equal
                  (withPolicy.Server
                   |> Option.map (fun s -> s.Constraints |> List.map _.Capability))
                  (Some [ "ApplyOps" ])
                  "the host's bound on the arm rides the same document"
          }

          test "ADVERSARY W3 — an off-list publish target is refused before anything performs" {
              let world = seeded ()

              let elsewhere =
                  { archive with
                      Stages = archive.Stages @ [ Effect(ServerEffect.ApplyOps [ Publish "upstream" ]) ] }

              let outcome = run world None elsewhere

              Expect.isFalse outcome.Committed "refused"
              Expect.isEmpty outcome.Performed "nothing performed"
              Expect.isEmpty world.Invocations "the performer was never asked"
              Expect.equal (world.Files |> Map.toList) [ "notes/x.md", "live" ] "the world is untouched"
              Expect.isEmpty world.Published "nothing published"

              Expect.equal
                  (outcome.Diagnostics |> List.last)
                  (ServerDiagnostic.Failed("ApplyOps", "argument-not-allowed:target"))
                  "refused while planning, naming the argument the host bounded and never the value"
          }

          test "ADVERSARY W4 — the destination CLASS binds: a remote the policy does not name is refused by class" {
              // A policy that names no `target` at all but bounds the
              // destination class still refuses a publish to an unnamed remote:
              // the bound is on where the op reaches, not on how the domain
              // spells it.
              let byClass =
                  ServerEffectRegistry.permissive ServerEffectRegistry.denyAll
                  |> ServerEffectRegistry.constrain
                      "ApplyOps"
                      [ ServerConstraintClause.AllowList(ServerArgumentPolicy.DestinationArgument, [ "local" ]) ]

              let world = seeded ()

              let outcome =
                  runIn
                      byClass
                      world
                      None
                      { Name = "push"
                        Stages = [ Effect(ServerEffect.ApplyOps [ Write("notes/x.md", "x"); Publish "origin" ]) ] }
                      empty

              Expect.isFalse outcome.Committed "refused"
              Expect.isEmpty world.Invocations "before anything performs"

              Expect.equal
                  (outcome.Diagnostics |> List.last)
                  (ServerDiagnostic.Failed(
                      "ApplyOps",
                      "argument-not-allowed:" + ServerArgumentPolicy.DestinationArgument
                  ))
                  "the local write passed; the remote publish is off the class list"
          }

          test "a ceiling on the arm measures the ops' canonical bytes" {
              let bounded =
                  ServerEffectRegistry.permissive ServerEffectRegistry.denyAll
                  |> ServerEffectRegistry.constrain "ApplyOps" [ ServerConstraintClause.Ceiling 64 ]

              let world = World()

              let outcome (content: string) =
                  runIn
                      bounded
                      world
                      None
                      { Name = "write"
                        Stages = [ Effect(ServerEffect.ApplyOps [ Write("a.md", content) ]) ] }
                      empty

              Expect.isTrue (outcome "small").Committed "under the ceiling"
              Expect.isFalse (outcome (String.replicate 64 "x")).Committed "over it"

              Expect.equal
                  ((outcome (String.replicate 64 "x")).Diagnostics |> List.last)
                  (ServerDiagnostic.Failed("ApplyOps", "payload-over-ceiling:64"))
                  "naming the limit, never the size"
          }

          // ── F1: a guard that halts — on the op channel, over the plan ──

          test "ADVERSARY F1 — a guard that does not hold halts the handler with nothing performed" {
              // The archive copy already exists in the world, so the plan's
              // `Missing` check after the delete holds — but a run whose
              // delete is absent leaves the note in the PLAN, and the guard
              // sees the plan.
              let world = seeded ()

              let keeps =
                  { Name = "keeps"
                    Stages =
                      [ Effect(ServerEffect.ApplyOps [ Write("notes/archive/x.md", "archived") ])
                        Effect(ServerEffect.ApplyOps [ Check(Missing "notes/x.md"); Publish "origin" ]) ] }

              let outcome = run world None keeps

              Expect.isFalse outcome.Committed "halted"
              Expect.isEmpty outcome.Performed "nothing performed"
              Expect.isEmpty world.Invocations "the performer was never asked — not even for the write before the guard"
              Expect.equal (world.Files |> Map.toList) [ "notes/x.md", "live" ] "the world is untouched"

              Expect.equal
                  outcome.Diagnostics
                  [ ServerDiagnostic.Failed(
                        "ApplyOps",
                        VerbRefusal.render
                            { Code = "present"
                              Detail = "notes/x.md" }
                    ) ]
                  "the guard's own refusal is the whole record of why"

              Expect.equal outcome.Store.Tree.Files world.Files "the state is the entry state"
              Expect.isEmpty world.Published "and the publish after the guard never performed"
          }

          test "a guard reads the PLANNED state, not the entry state" {
              // The entry world holds the note; the plan deletes it; a check
              // that it exists, placed after the delete, refuses — because it
              // reads the state the ops before it produced.
              let world = seeded ()

              let outcome =
                  run
                      world
                      None
                      { Name = "after-delete"
                        Stages = [ Effect(ServerEffect.ApplyOps [ Delete "notes/x.md"; Check(Exists "notes/x.md") ]) ] }

              Expect.isFalse outcome.Committed "the guard saw the delete"
              Expect.isEmpty world.Invocations "nothing performed"

              Expect.equal
                  outcome.Diagnostics
                  [ ServerDiagnostic.Failed(
                        "ApplyOps",
                        VerbRefusal.render
                            { Code = "missing"
                              Detail = "notes/x.md" }
                    ) ]
                  "refused on the plan"
          }

          // ── W5: a typed refusal crosses as text ──

          test "W5 — a typed refusal crosses the guard as canonical JSON and parses back on the far side" {
              let refusal =
                  { Code = "bundle-ambiguous"
                    Detail = "x matches 2 bundles: x-a, x-b" }

              let world = seeded ()

              let outcome =
                  run
                      world
                      None
                      { Name = "ambiguous"
                        Stages = [ Effect(ServerEffect.ApplyOps [ Check(Refused refusal); Publish "origin" ]) ] }

              Expect.isFalse outcome.Committed "halted"
              Expect.isEmpty world.Invocations "nothing performed"

              match outcome.Diagnostics with
              | [ ServerDiagnostic.Failed("ApplyOps", reason) ] ->
                  Expect.equal
                      (VerbRefusal.parse reason)
                      (Some refusal)
                      "the domain's typed refusal, back from the text"
              | other -> failtestf "expected the guard's refusal, got %A" other
          }

          // ── F2: the plan is performed, and a part-way failure is positioned ──

          test "ADVERSARY F2 — a part-way performance failure reports the prefix that ran and where it stopped" {
              let world = seeded ()
              let outcome = run world (Some 2) archive

              Expect.isFalse outcome.Committed "rolled back"

              Expect.equal
                  outcome.Performed
                  [ "ApplyOps"; "ApplyOps" ]
                  "the two ops that ran before the refusal — the read and the write — and nothing else"

              Expect.equal
                  (outcome.Diagnostics |> List.last)
                  (ServerDiagnostic.PerformFailed("ApplyOps", "the world refused op 2"))
                  "a `PerformFailed` under the op's capability, with the performer's own reason"

              Expect.equal
                  (world.Files |> Map.toList)
                  [ "notes/archive/x.md", "archived"; "notes/x.md", "live" ]
                  "the world holds the residue: written, not yet deleted"

              Expect.isEmpty world.Published "the publish after the failure never ran"
              Expect.equal outcome.Store.Tree.Files (Map.ofList [ "notes/x.md", "live" ]) "the plan is discarded"
              Expect.equal (List.length world.Invocations) 3 "the performer was asked three times and stopped"
          }

          // ── Phase 1981: the performer's claim is checked against the op's reach ──

          test "a checked performer whose receipts stay within each op's reach commits exactly as the unchecked one" {
              let world = seeded ()

              let outcome =
                  runPerforming
                      world
                      (OpPerformance.performedChecked [ Receipt.withinReach ] (fun _ state op ->
                          world.Performer None state op |> Result.map OpReceipt.ofDetail))
                      archive

              Expect.isTrue outcome.Committed "every receipt named only what its op's reach declared"

              Expect.equal
                  outcome.Performed
                  [ "ApplyOps"; "ApplyOps"; "ApplyOps"; "ApplyOps" ]
                  "the four edits performed, each its own staged call, as without the contract"

              Expect.equal
                  (world.Files |> Map.toList)
                  [ "notes/archive/x.md", "archived" ]
                  "and the world is what the unchecked performer leaves"

              Expect.equal world.Published [ "origin" ] "published"
          }

          test
              "ADVERSARY 1981 — a performer that touches a path outside the op's reach is refused by the contract, and the op is not reported as performed" {
              let world = seeded ()
              let escape = "etc/passwd"

              let outcome =
                  runPerforming
                      world
                      (OpPerformance.performedChecked [ Receipt.withinReach ] (fun _ state op ->
                          world.Escaping escape None state op |> Result.map OpReceipt.ofDetail))
                      archive

              Expect.isFalse outcome.Committed "rolled back"

              Expect.equal
                  outcome.Performed
                  [ "ApplyOps" ]
                  "the read before the write ran and is reported; the write whose receipt overreached is NOT"

              Expect.equal
                  (outcome.Diagnostics |> List.last)
                  (ServerDiagnostic.PerformFailed("ApplyOps", "return-contract:within-reach"))
                  "a `PerformFailed` under the op's capability naming the CONTRACT — never the receipt, never the path"

              Expect.isFalse
                  (outcome.Diagnostics |> List.exists (fun d -> (sprintf "%A" d).Contains escape))
                  "the escaped path appears in no diagnostic: a refusal names the contract, not the claim"

              Expect.equal
                  (world.Files |> Map.toList)
                  [ escape, "archived"; "notes/archive/x.md", "archived"; "notes/x.md", "live" ]
                  "the world holds what the adversary did — the write within reach AND the escape — because a \
                   contract checks the claim, it does not undo the act: the residue is reported, not hidden"

              Expect.isEmpty world.Published "nothing after the refused op ran"
              Expect.equal outcome.Store.Tree.Files (Map.ofList [ "notes/x.md", "live" ]) "the plan is discarded"
              Expect.equal (List.length world.Invocations) 2 "the performer was asked twice and stopped"
          }

          test "the contract is handed the planned state and the op, and reads the receipt beside them" {
              // The contract's three arguments, pinned: a contract that could
              // not see the op could not know its reach, and one that could not
              // see the state could not check a receipt against what the plan
              // produced.
              let world = seeded ()
              let seen = System.Collections.Generic.List<string * string>()

              let recording: OpContract<FileMap, FileOp> =
                  { Name = "recording"
                    Holds =
                      fun prefix state op receipt ->
                          seen.Add(encodeOp op, canonical state)
                          Receipt.withinReach.Holds prefix state op receipt }

              let outcome =
                  runPerforming
                      world
                      (OpPerformance.performedChecked [ recording ] (fun _ state op ->
                          world.Performer None state op |> Result.map OpReceipt.ofDetail))
                      archive

              Expect.isTrue outcome.Committed "committed"

              Expect.equal
                  (seen |> Seq.map fst |> List.ofSeq)
                  world.Invocations
                  "the contract saw each op the performer was handed, in order"

              Expect.equal
                  (seen |> Seq.map snd |> List.ofSeq)
                  (world.Handed |> List.map canonical)
                  "and the planned state the performer was handed with it"
          }

          test "a raw refusal passes through a contract unchanged, with the performer's own reason" {
              let world = seeded ()

              let outcome =
                  runPerforming
                      world
                      (OpPerformance.performedChecked [ Receipt.withinReach ] (fun _ state op ->
                          world.Performer (Some 2) state op |> Result.map OpReceipt.ofDetail))
                      archive

              Expect.isFalse outcome.Committed "rolled back"

              Expect.equal
                  (outcome.Diagnostics |> List.last)
                  (ServerDiagnostic.PerformFailed("ApplyOps", "the world refused op 2"))
                  "the refusal is the performer's, not the contract's"
          }

          test "F-PERFORM — the performer is handed the planned state as of each op, and the last is the plan" {
              let world = seeded ()
              let outcome = run world None archive

              Expect.isTrue outcome.Committed "committed"

              Expect.equal
                  (world.Handed |> List.map (fun s -> s.Files |> Map.toList, s.Published))
                  [ [ "notes/x.md", "live" ], []
                    [ "notes/archive/x.md", "archived"; "notes/x.md", "live" ], []
                    [ "notes/archive/x.md", "archived" ], []
                    [ "notes/archive/x.md", "archived" ], [ "origin" ] ]
                  "each edit handed the state it produced"

              Expect.equal (List.last world.Handed) outcome.Store.Tree "and the last handed state IS the committed plan"
          }

          test "in memory, the same verb performs nothing outside — the apply is the effect" {
              let world = seeded ()

              let outcome =
                  Handler.run
                      witness
                      registry
                      DataFrame.noResolve
                      "verb"
                      archive
                      { Tree = { empty with Files = world.Files }
                        Bindings = () }

              Expect.isTrue outcome.Committed "committed"
              Expect.equal outcome.Performed [ "ApplyOps"; "ApplyOps"; "ApplyOps" ] "once per effect, at plan time"
              Expect.isEmpty world.Invocations "no performer was registered, so none ran"
              Expect.equal (world.Files |> Map.toList) [ "notes/x.md", "live" ] "the world is untouched"
              Expect.equal outcome.Store.Tree.Published [ "origin" ] "the tree — the in-memory plan — is the state"
          }

          test "an apply refusal halts while planning, so a performer registered or not sees nothing" {
              let world = World()

              let outcome =
                  run
                      world
                      None
                      { Name = "read-missing"
                        Stages = [ Effect(ServerEffect.ApplyOps [ Read "notes/x.md" ]) ] }

              Expect.isFalse outcome.Committed "the read of a missing note refuses the apply"
              Expect.isEmpty world.Invocations "nothing performed"

              Expect.equal
                  (outcome.Diagnostics |> List.last)
                  (ServerDiagnostic.Failed("ApplyOps", "no such file: notes/x.md"))
                  "the apply's own refusal"
          }

          // ── no dispatch axis: no binding channel ──

          test "a landing slot under a state-only witness is refused while planning — there is no binding channel" {
              let world = seeded ()
              let called = ref false

              let withHost =
                  ServerEffectRegistry.permissive ServerEffectRegistry.denyAll
                  |> ServerEffectRegistry.register "fetch" (fun _ ->
                      called.Value <- true
                      Ok(JStr "ran"))

              let landing =
                  runIn
                      withHost
                      world
                      None
                      { Name = "lands"
                        Stages = [ Effect(ServerEffect.HostCall("fetch", JObj [], Some "result")) ] }
                      empty

              Expect.isFalse landing.Committed "refused"
              Expect.isFalse called.Value "the host function was never invoked"

              Expect.equal
                  landing.Diagnostics
                  [ ServerDiagnostic.Failed("host:fetch", Handler.NoBindingChannel) ]
                  "named, through the landing-slot halt"

              let query =
                  runIn
                      withHost
                      world
                      None
                      { Name = "reads"
                        Stages = [ Effect(ServerEffect.RunQuery("rows", Fuaran.Core.Ref "anything", [])) ] }
                      empty

              Expect.equal
                  query.Diagnostics
                  [ ServerDiagnostic.Failed("RunQuery", Handler.NoBindingChannel) ]
                  "a query has nowhere to land either, so it is refused before it reads"

              let noLanding =
                  runIn
                      withHost
                      world
                      None
                      { Name = "calls"
                        Stages = [ Effect(ServerEffect.HostCall("fetch", JObj [], None)) ] }
                      empty

              Expect.isTrue noLanding.Committed "a host call that lands nothing needs no channel"
              Expect.isTrue called.Value "and runs"
          }

          // ── Phase 1976: selection and bounded iteration on the op axis ──────

          test "a two-arm branch whose arms both continue, planned IN Program, ends in different outcomes" {
              let present = seeded ()
              let took = flowRun present migrate
              Expect.isTrue took.Committed "the true arm commits"

              Expect.equal
                  (present.Files |> Map.toList)
                  [ "notes/x.md", "migrated" ]
                  "the true arm migrated, and left no marker"

              Expect.equal
                  took.Performed
                  [ "ApplyOps"; "ApplyOps" ]
                  "one edit and the publish performed; the conditions never"

              Expect.equal present.Published [ "origin" ] "and the sequence continued past the branch"

              let absent = World()
              let created = flowRun absent migrate
              Expect.isTrue created.Committed "the false arm commits"

              Expect.equal
                  (absent.Files |> Map.toList)
                  [ "notes/created.marker", ""; "notes/x.md", "created" ]
                  "the false arm created, with the marker"

              Expect.equal created.Performed [ "ApplyOps"; "ApplyOps"; "ApplyOps" ] "two edits and the publish"
              Expect.notEqual took.Store.Tree created.Store.Tree "two arms, two outcomes"

              Expect.isFalse
                  (absent.Invocations
                   |> List.exists (fun op -> op.Contains "Exists" || op.Contains "Missing"))
                  "no condition reached the performer"
          }

          test
              "a violated exit assertion refuses the effect after the arm planned, naming the assertion, with nothing performed" {
              let world = seeded ()

              // The true arm leaves the marker it must not: the exit assertion
              // fails after the true arm.
              let broken =
                  { Name = "broken"
                    Stages =
                      [ Effect(
                            ServerEffect.ApplyOps
                                [ Branch(
                                      Exists "notes/x.md",
                                      [ Write("notes/created.marker", "") ],
                                      [],
                                      Some(Missing "notes/created.marker")
                                  )
                                  Publish "origin" ]
                        ) ] }

              let outcome = flowRun world broken
              Expect.isFalse outcome.Committed "halted"
              Expect.isEmpty outcome.Performed "nothing performed"
              Expect.isEmpty world.Invocations "the performer was never asked"
              Expect.equal (world.Files |> Map.toList) [ "notes/x.md", "live" ] "the world is untouched"

              Expect.equal
                  outcome.Diagnostics
                  [ ServerDiagnostic.Failed(
                        "ApplyOps",
                        "the exit assertion did not hold after the true arm: "
                        + VerbRefusal.render
                            { Code = "present"
                              Detail = "notes/created.marker" }
                    ) ]
                  "the assertion's own refusal names it"

              // And the other way: an exit assertion that HOLDS after the
              // false arm is the same defect.
              let heldAfterFalse =
                  { Name = "held"
                    Stages =
                      [ Effect(
                            ServerEffect.ApplyOps
                                [ Branch(Missing "notes/x.md", [], [ Publish "origin" ], Some(Exists "notes/x.md")) ]
                        ) ] }

              let world' = seeded ()
              let outcome' = flowRun world' heldAfterFalse
              Expect.isFalse outcome'.Committed "halted"
              Expect.isEmpty world'.Published "the arm's publish was planned, never performed"

              Expect.equal
                  outcome'.Diagnostics
                  [ ServerDiagnostic.Failed("ApplyOps", "the exit assertion held after the false arm") ]
                  "named the other way"
          }

          test
              "a condition that refuses takes the false arm: on the op channel a typed refusal is the false value, not a halt" {
              let world = seeded ()

              let refusing =
                  { Name = "refusing"
                    Stages =
                      [ Effect(
                            ServerEffect.ApplyOps
                                [ Branch(
                                      Refused { Code = "undecided"; Detail = "x" },
                                      [ Write("notes/x.md", "true") ],
                                      [ Write("notes/x.md", "false") ],
                                      None
                                  ) ]
                        ) ] }

              let outcome = flowRun world refusing
              Expect.isTrue outcome.Committed "no halt"
              Expect.equal world.Files.["notes/x.md"] "false" "the false arm ran"
              Expect.isEmpty outcome.Diagnostics "and the refusal is not a diagnostic — it was the answer"
          }

          test
              "a bounded repeat plans its body that many times; an over-bound count is refused by the policy before anything performs" {
              let world = seeded ()

              let thrice =
                  { Name = "thrice"
                    Stages = [ Effect(ServerEffect.ApplyOps [ Times(3, [ Publish "origin" ]) ]) ] }

              let outcome = flowRun world thrice
              Expect.isTrue outcome.Committed "commits"
              Expect.equal world.Published [ "origin"; "origin"; "origin" ] "three publishes, in order"
              Expect.equal outcome.Performed [ "ApplyOps"; "ApplyOps"; "ApplyOps" ] "three staged edits"

              let world' = seeded ()

              let tooMany =
                  { Name = "too-many"
                    Stages = [ Effect(ServerEffect.ApplyOps [ Times(4, [ Publish "origin" ]) ]) ] }

              let refused = flowRun world' tooMany
              Expect.isFalse refused.Committed "refused"
              Expect.isEmpty refused.Performed "nothing performed"
              Expect.isEmpty world'.Invocations "the performer was never asked"
              Expect.isEmpty world'.Published "nothing published"

              Expect.equal
                  (refused.Diagnostics |> List.last)
                  (ServerDiagnostic.Failed("ApplyOps", "argument-not-allowed:count"))
                  "refused while planning, naming the argument the host bounded — the count — and never the value"
          }

          test "the demanded document carries BOTH arms' reach, and the policy binds the untaken arm" {
              let projection = ServerDemanded.ofHandler witness migrate

              let tier =
                  match projection.Server with
                  | Some tier -> tier
                  | None -> failtest "the walk ran, so the document must carry a server tier"

              let reach = tier.Reach |> List.map (fun r -> r.Argument, r.Name)
              Expect.contains reach ("path", "notes/created.marker") "the false arm's marker path is in the document"
              Expect.contains reach ("path", "notes/x.md") "and the shared path"
              Expect.contains reach ("target", "origin") "and the publish target after the branch"

              // An arm the run would NOT take still reaches: under the archive
              // policy, which does not name the marker path, the branch is
              // refused even though the true arm — which never touches the
              // marker — is the one that would run.
              let present = seeded ()
              let outcome = run present None migrate
              Expect.isFalse outcome.Committed "refused by the policy: the untaken arm reaches an off-list path"
              Expect.isEmpty present.Invocations "before anything performed"
              Expect.equal (present.Files |> Map.toList) [ "notes/x.md", "live" ] "the world is untouched"

              Expect.equal
                  (outcome.Diagnostics |> List.last)
                  (ServerDiagnostic.Failed("ApplyOps", "argument-not-allowed:path"))
                  "naming the argument"
          } ]

// ─── Phase 1977: the undo posture, and the undo run ─────────────────────────

/// The archive policy, widened for the undo tests: the staging target a
/// publish can be retracted from, and a path the reversible verb creates.
let private undoRegistry: ServerEffectRegistry =
    ServerEffectRegistry.permissive ServerEffectRegistry.denyAll
    |> ServerEffectRegistry.constrain
        "ApplyOps"
        [ ServerConstraintClause.AllowList("path", [ "notes/x.md"; "notes/archive/x.md"; "notes/y.md" ])
          ServerConstraintClause.AllowList("target", [ "origin"; "staging" ])
          ServerConstraintClause.AllowList(ServerArgumentPolicy.DestinationArgument, [ "local"; "origin"; "staging" ]) ]

/// REVERSIBLE: writes and a delete, every one with an exact inverse.
let private rewrite: VerbHandler =
    { Name = "rewrite"
      Stages =
        [ Effect(ServerEffect.ApplyOps [ Check(Exists "notes/x.md"); Write("notes/x.md", "rewritten") ])
          Effect(ServerEffect.ApplyOps [ Write("notes/y.md", "new"); Delete "notes/archive/x.md" ]) ] }

/// COMPENSABLE: a write, then a publish to the staging target, whose
/// retraction the domain declares.
let private stage: VerbHandler =
    { Name = "stage"
      Stages = [ Effect(ServerEffect.ApplyOps [ Write("notes/x.md", "staged"); Publish "staging" ]) ] }

/// ONE-WAY: a write, then a publish to origin, which is public and carries
/// no compensation — the expected case of a verb that ends in a push.
let private push: VerbHandler =
    { Name = "push"
      Stages =
        [ Effect(ServerEffect.ApplyOps [ Write("notes/x.md", "pushed") ])
          Effect(ServerEffect.ApplyOps [ Publish "origin" ]) ] }

/// Run a handler and keep its plan, under the undo registry.
let private planned (world: World) (failAt: int option) (handler: VerbHandler) =
    Handler.runPlanned
        witness
        undoRegistry
        (OpPerformance.performedWithDetail (world.Performer failAt))
        DataFrame.noResolve
        "verb"
        handler
        { Tree = { empty with Files = world.Files }
          Bindings = () }

/// Undo a plan against the store the run left, through the same world.
let private undoIn (world: World) (failAt: int option) plan post =
    Undo.run
        witness
        undoRegistry
        (OpPerformance.performedWithDetail (world.Performer failAt))
        DataFrame.noResolve
        "verb"
        plan
        post

let private undoOf (handler: VerbHandler) =
    Undo.posture QueryPosture.PureRead witness handler, Undo.reasons QueryPosture.PureRead witness handler

let private stepText (step: UndoStep<FileMap, FileOp, Nothing>) =
    match step with
    | UndoStep.Edit(pre, op) -> sprintf "edit %s before %s" (encodeOp op) (canonical pre)
    | UndoStep.Compute _ -> "compute"
    | UndoStep.Reached capability -> "reached " + capability
    | UndoStep.Emitted capability -> "emitted " + capability

[<Tests>]
let undoTests =
    testList
        "Phase 1977 — the undo posture over the verb"
        [ test "the posture is read off the declared form: reversible, compensable, one-way, with the stage named" {
              Expect.equal
                  (undoOf rewrite)
                  (UndoVerdict.Reversible, [])
                  "writes and a delete: every edit has an exact inverse"

              Expect.equal
                  (undoOf stage)
                  (UndoVerdict.Compensable,
                   [ { UndoReason.Stage = 0
                       Defect = UndoDefect.CompensatedOp } ])
                  "a publish to staging is compensable, by the domain's declared retraction"

              Expect.equal
                  (undoOf push)
                  (UndoVerdict.OneWay,
                   [ { UndoReason.Stage = 1
                       Defect = UndoDefect.OneWayOp } ])
                  "a publish to origin is one-way, and the posture names the stage: everything before it can be undone"

              Expect.equal
                  (undoOf archive)
                  (UndoVerdict.OneWay,
                   [ { UndoReason.Stage = 2
                       Defect = UndoDefect.OneWayOp } ])
                  "the archive verb is undoable up to its push and one-way at it"
          }

          test "the demanded document carries the undo posture per handler, beside the replay posture" {
              let handlers = [ rewrite; stage; push ]

              let projection =
                  ServerDemanded.ofHandlers witness handlers
                  |> Undo.withPostures QueryPosture.PureRead witness handlers

              let tier =
                  match projection.Server with
                  | Some tier -> tier
                  | None -> failtest "the walk ran, so the document must carry a server tier"

              Expect.equal
                  (tier.Undo
                   |> List.map (fun p -> p.Handler, p.Undo, p.Reasons |> List.map (fun r -> r.Stage, r.Defect)))
                  [ "push", "one-way", [ 1, "one-way-op" ]
                    "rewrite", "reversible", []
                    "stage", "compensable", [ 0, "compensated-op" ] ]
                  "one posture per handler, by name, reasons in stage order with the wire tokens"

              // The document's bytes carry it at version 7 (Phase 1991), and read back.
              let json = Demanded.encode projection

              Expect.stringContains
                  json
                  $"\"version\":{Demanded.Version}"
                  "the undo posture rides the version this release emits"

              Expect.stringContains
                  json
                  "\"undo\":[{\"handler\":\"push\",\"undo\":\"one-way\",\"reasons\":[{\"stage\":1,\"defect\":\"one-way-op\"}]}"
                  "the posture's bytes"

              match Demanded.decode json with
              | Ok read -> Expect.equal read projection "the document reads back as the projection"
              | Error failure -> failtestf "the document does not read back: %A" failure
          }

          test "a REVERSIBLE run is undone to the pre-state, byte for byte, through the same performers" {
              let world = seeded ()
              world.Seed("notes/archive/x.md", "old")
              let entry = { empty with Files = world.Files }
              let outcome, plan = planned world None rewrite
              Expect.isTrue outcome.Committed "the run commits"
              Expect.isTrue plan.Committed "and its plan says so"

              Expect.equal
                  (world.Files |> Map.toList)
                  [ "notes/x.md", "rewritten"; "notes/y.md", "new" ]
                  "the world was rewritten, created and deleted"

              let afterFirst =
                  { entry with
                      Files = Map.add "notes/x.md" "rewritten" entry.Files }

              let afterSecond =
                  { afterFirst with
                      Files = Map.add "notes/y.md" "new" afterFirst.Files }

              Expect.equal
                  (plan.Steps |> List.map stepText)
                  [ stepText (UndoStep.Edit(entry, Write("notes/x.md", "rewritten")))
                    stepText (UndoStep.Edit(afterFirst, Write("notes/y.md", "new")))
                    stepText (UndoStep.Edit(afterSecond, Delete "notes/archive/x.md")) ]
                  "the plan records every EDIT with the state it was applied to, in plan order; the guard is not a step"

              match undoIn world None plan outcome.Store with
              | Error refusal -> failtestf "the undo was refused: %s" (Undo.describe refusal)
              | Ok undone ->
                  Expect.isTrue undone.Committed "the undo commits"

                  Expect.equal
                      (canonical undone.Store.Tree)
                      (canonical entry)
                      "the state is the entry state, byte for byte"

                  Expect.equal (world.Files |> Map.toList) (entry.Files |> Map.toList) "and so is the world"

                  Expect.equal
                      (world.Invocations |> List.skip 3)
                      [ encodeOp (Write("notes/archive/x.md", "old"))
                        encodeOp (Delete "notes/y.md")
                        encodeOp (Write("notes/x.md", "live")) ]
                      "the inverses performed in REVERSE plan order: the delete restored, the creation deleted, the rewrite rewritten"

                  Expect.equal undone.Performed [ "ApplyOps"; "ApplyOps"; "ApplyOps" ] "one staged call per inverse"
          }

          test "a COMPENSABLE run reaches the compensated state: the publish retracted, the write restored" {
              let world = seeded ()
              let outcome, plan = planned world None stage
              Expect.isTrue outcome.Committed "the run commits"
              Expect.equal world.Published [ "staging" ] "published to staging"

              match undoIn world None plan outcome.Store with
              | Error refusal -> failtestf "the undo was refused: %s" (Undo.describe refusal)
              | Ok undone ->
                  Expect.isTrue undone.Committed "the undo commits"
                  Expect.isEmpty world.Published "the publish was retracted"
                  Expect.equal (world.Files |> Map.toList) [ "notes/x.md", "live" ] "the write was restored"

                  Expect.equal
                      (world.Invocations |> List.skip 2)
                      [ encodeOp (Retract "staging"); encodeOp (Write("notes/x.md", "live")) ]
                      "the retraction first, then the inverse write: reverse plan order"

                  // Undone in effect, not in history: the plan's store reached
                  // the compensated state — here the entry state too, because
                  // a retraction removes the target.
                  Expect.equal
                      (canonical undone.Store.Tree)
                      (canonical
                          { empty with
                              Files = Map.ofList [ "notes/x.md", "live" ] })
                      "the compensated state"
          }

          test "a ONE-WAY step is refused before anything is undone, naming it" {
              let world = seeded ()
              let outcome, plan = planned world None push
              Expect.isTrue outcome.Committed "the run commits"
              Expect.equal world.Published [ "origin" ] "pushed"
              let before = world.Invocations

              match undoIn world None plan outcome.Store with
              | Ok _ -> failtest "a plan with a one-way step was undone"
              | Error refusal ->
                  Expect.equal refusal.Code UndoCode.OneWayStep "the one-way code"
                  Expect.equal refusal.Step 1 "the ordinal in the plan: the write is step 0, the publish step 1"
                  Expect.equal refusal.Reason "a publish to origin is public" "the domain's own reason"
                  Expect.equal (Undo.describe refusal) "undo-one-way-step@1: a publish to origin is public" "rendered"

              Expect.equal world.Invocations before "no performer was asked"
              Expect.equal (world.Files |> Map.toList) [ "notes/x.md", "pushed" ] "the world is as the run left it"
              Expect.equal world.Published [ "origin" ] "and so is the publish"
          }

          test "a failed undo step reports how far it got, in the perform-failure vocabulary" {
              let world = seeded ()
              world.Seed("notes/archive/x.md", "old")
              let outcome, plan = planned world None rewrite
              Expect.isTrue outcome.Committed "the run commits"

              // The undo's SECOND inverse refuses: the first ran and is not
              // taken back; the rest never ran.
              let undoWorld = World()

              for path, content in Map.toList world.Files do
                  undoWorld.Seed(path, content)

              match undoIn undoWorld (Some 1) plan outcome.Store with
              | Error refusal -> failtestf "the undo was refused: %s" (Undo.describe refusal)
              | Ok undone ->
                  Expect.isFalse undone.Committed "the undo rolled back"
                  Expect.equal undone.Performed [ "ApplyOps" ] "exactly the prefix that ran: one inverse"

                  Expect.equal
                      (undone.Diagnostics |> List.last)
                      (ServerDiagnostic.PerformFailed("ApplyOps", "the world refused op 1"))
                      "the failure names the capability and the performer's reason"

                  Expect.equal
                      (undoWorld.Files |> Map.toList)
                      [ "notes/archive/x.md", "old"; "notes/x.md", "rewritten"; "notes/y.md", "new" ]
                      "the first inverse, the delete restored, reached the world; the second did not"

                  Expect.equal
                      (canonical undone.Store.Tree)
                      (canonical outcome.Store.Tree)
                      "the undo's store is the one the run left"
          }

          test "a witness whose inverse breaks its law is refused rather than performed" {
              // The same verb, with a write's inverse that lies: it restores the
              // wrong bytes. The plan folds to a state that is not the entry
              // state, and the undo refuses before any performer is asked.
              let lying =
                  { witness with
                      State =
                          { witness.State with
                              Undo =
                                  fun op ->
                                      match op with
                                      | Write(path, _) -> UndoClass.Inverse(fun _ -> [ Write(path, "wrong") ])
                                      | other -> undo other } }

              let world = seeded ()

              let writing: VerbHandler =
                  { Name = "write"
                    Stages = [ Effect(ServerEffect.ApplyOps [ Write("notes/x.md", "x") ]) ] }

              let outcome, plan =
                  Handler.runPlanned
                      lying
                      undoRegistry
                      (OpPerformance.performedWithDetail (world.Performer None))
                      DataFrame.noResolve
                      "verb"
                      writing
                      { Tree = { empty with Files = world.Files }
                        Bindings = () }

              Expect.isTrue outcome.Committed "the run commits"
              let before = world.Invocations

              match
                  Undo.run
                      lying
                      undoRegistry
                      (OpPerformance.performedWithDetail (world.Performer None))
                      DataFrame.noResolve
                      "verb"
                      plan
                      outcome.Store
              with
              | Ok _ -> failtest "a lying inverse was performed"
              | Error refusal -> Expect.equal refusal.Code UndoCode.InverseDrift "refused for drift"

              Expect.equal world.Invocations before "no performer was asked"
          }

          test "a plan that rolled back has nothing to undo, and says so" {
              let world = seeded ()
              let outcome, plan = planned world (Some 0) rewrite
              Expect.isFalse outcome.Committed "the run rolled back"

              match undoIn world None plan outcome.Store with
              | Ok _ -> failtest "an uncommitted plan was undone"
              | Error refusal -> Expect.equal refusal.Code UndoCode.UncommittedPlan "named"
          } ]

// ─── Phase 2828: the op channel carries a structured refusal ────────────────

/// A refusal the verb's condition raises when it is asked before what it reads
/// exists: the program is wrong, not the answer "no".
let private notDraft = OpRefusal.malformed "not-draft" "tested before any load"

/// The report a caller receives of an outcome, encoded as the specification's
/// outcome document.
let private reportOf (outcome: HandlerOutcome<FileMap, unit, FileOp, Nothing>) : string =
    match HandlerWire.encodeReport witness (HandlerReport.ofOutcome outcome) with
    | Ok text -> text
    | Error refusal -> failtestf "the report did not encode: %A" refusal

/// A store's own codec for a text record: any content is the record.
let private textCodec: ReadCodec<string> = { Name = "text"; Decode = Ok }

/// The verb witness whose `Exists` check over a `store/` path READS the store
/// through Program's typed reads, and answers the run's own unavailable-read
/// refusal when the read could not answer: Program's refusal, on the channel.
let private readingWitness (reads: Reads) =
    { witness with
        State =
            { witness.State with
                Stream =
                    { witness.State.Stream with
                        Apply =
                            fun op tree ->
                                match op with
                                | Check(Exists path) when path.StartsWith "store/" ->
                                    match reads.Read(textCodec, path, (fun () -> Error "the store is unreachable")) with
                                    | Error tier -> Error tier
                                    | Ok(Read.Available _) -> Ok tree
                                    | Ok(Read.Unavailable _) -> Error(Option.get (reads.Refusal()))
                                | _ -> apply op tree } } }

[<Tests>]
let refusalTests =
    testList
        "Phase 2828 — the op channel carries a structured refusal"
        [ test "the canonical form round-trips per class, and the report carries its discriminator" {
              for refusal in
                  [ OpRefusal.refused "no-draft" "the report is final"
                    notDraft
                    OpRefusal.unavailable "read-unavailable" "index (not-read: gone); notes: a: b" ] do
                  Expect.equal (OpRefusal.tryParse (OpRefusal.render refusal)) (Some refusal) "back from the text"
                  Expect.equal (OpRefusal.parse (OpRefusal.render refusal)) refusal "and through the total reading"

              Expect.equal (OpRefusal.render notDraft) "malformed:not-draft: tested before any load" "the spelling"
              Expect.equal (OpRefusal.discriminator notDraft) "malformed:not-draft" "the discriminator"

              Expect.equal
                  (OpRefusal.render (OpRefusal.malformed "draft" ""))
                  "malformed:draft"
                  "an empty detail is not written"

              Expect.equal
                  (OpRefusal.tryParse "unavailable:-: nothing named")
                  (Some
                      { Class = OpRefusalClass.Unavailable
                        Code = None
                        Detail = "nothing named" })
                  "`-` is the spelling of no code"
          }

          test "an ill-written code is normalised, and the refusal keeps its class" {
              let refusal = OpRefusal.malformed "not draft:yet" "x"

              Expect.equal (OpRefusal.render refusal) "malformed:not-draft-yet: x" "written as a token"

              Expect.equal
                  (OpRefusal.tryParse (OpRefusal.render refusal) |> Option.map _.Class)
                  (Some OpRefusalClass.Malformed)
                  "the class survives the crossing"

              Expect.isTrue (OpRefusal.halts (OpRefusal.render refusal)) "and still halts a branch"

              Expect.equal
                  (OpRefusal.render (OpRefusal.unavailable "" "x"))
                  "unavailable:-: x"
                  "an empty code is no code, never a lost class"
          }

          test "a reason not in the canonical form reads as refused with no code, the whole reason its detail" {
              for reason in
                  [ "malformed: not-draft tested before any load"
                    "no such file: notes/x.md"
                    VerbRefusal.render
                        { Code = "missing"
                          Detail = "notes/x.md" }
                    "refused:"
                    "malformed:x: "
                    "unavailable:a b: c"
                    "" ] do
                  Expect.isNone (OpRefusal.tryParse reason) (sprintf "%s is not canonical" reason)

                  Expect.equal
                      (OpRefusal.parse reason)
                      { Class = OpRefusalClass.Refused
                        Code = None
                        Detail = reason }
                      "refused, no code"

                  Expect.isFalse (OpRefusal.halts reason) "and the false answer, as before the form existed"
          }

          test
              "a branch whose condition is MALFORMED halts with that refusal: neither arm plans and the delete is never performed" {
              // The evidence, in the verb: a draft check that cannot be
              // answered before anything is loaded, guarding a delete in the
              // false arm, with the same check as the exit assertion, which
              // refuses too, as the false arm expects, so it never caught it.
              let world = seeded ()

              let outcome =
                  run
                      world
                      None
                      { Name = "archive-report"
                        Stages =
                          [ Effect(
                                ServerEffect.ApplyOps
                                    [ Branch(Raises notDraft, [], [ Delete "notes/x.md" ], Some(Raises notDraft)) ]
                            ) ] }

              Expect.isFalse outcome.Committed "halted"
              Expect.isEmpty outcome.Performed "nothing performed"
              Expect.isEmpty world.Invocations "the performer was never asked"
              Expect.equal (world.Files |> Map.toList) [ "notes/x.md", "live" ] "the file is still there"
              Expect.isEmpty outcome.Flow "and no arm was taken"

              Expect.equal
                  outcome.Diagnostics
                  [ ServerDiagnostic.Failed("ApplyOps", OpRefusal.render notDraft) ]
                  "the host's outcome holds the refusal whole"

              Expect.equal
                  (HandlerReport.ofOutcome outcome).Diagnostics
                  [ ServerDiagnostic.Failed("ApplyOps", "malformed:not-draft") ]
                  "the report carries its discriminator"
          }

          test "an UNAVAILABLE condition halts the same way" {
              let world = seeded ()
              let unknown = OpRefusal.unavailable "index" "the catalogue was not read"

              let outcome =
                  run
                      world
                      None
                      { Name = "unknown"
                        Stages =
                          [ Effect(
                                ServerEffect.ApplyOps
                                    [ Branch(Raises unknown, [ Publish "origin" ], [ Delete "notes/x.md" ], None) ]
                            ) ] }

              Expect.isFalse outcome.Committed "halted"
              Expect.isEmpty world.Invocations "nothing performed"
              Expect.isEmpty outcome.Flow "no arm"

              Expect.equal
                  outcome.Diagnostics
                  [ ServerDiagnostic.Failed("ApplyOps", OpRefusal.render unknown) ]
                  "on the refusal"
          }

          test "a domain REFUSED condition still takes the false arm" {
              let world = seeded ()

              let outcome =
                  run
                      world
                      None
                      { Name = "final"
                        Stages =
                          [ Effect(
                                ServerEffect.ApplyOps
                                    [ Branch(
                                          Raises(OpRefusal.refused "no-draft" "the report is final"),
                                          [ Write("notes/archive/x.md", "true") ],
                                          [ Delete "notes/x.md" ],
                                          None
                                      ) ]
                            ) ] }

              Expect.isTrue outcome.Committed "no halt"
              Expect.equal outcome.Flow [ FlowDecision.Chose false ] "the false arm"
              Expect.isEmpty outcome.Diagnostics "the refusal was the answer"
              Expect.isFalse (world.Files.ContainsKey "notes/x.md") "and the false arm's delete performed"
          }

          test "an unparsed reason behaves as it did before the form existed: the false arm, and the delete performed" {
              let world = seeded ()

              let undecided =
                  { Code = "undecided"
                    Detail = "not-draft tested before any load" }

              Expect.isNone
                  (OpRefusal.tryParse (VerbRefusal.render undecided))
                  "premise: the verb's own JSON is no canonical refusal"

              let outcome =
                  run
                      world
                      None
                      { Name = "legacy"
                        Stages =
                          [ Effect(
                                ServerEffect.ApplyOps
                                    [ Branch(Refused undecided, [], [ Delete "notes/x.md" ], Some(Refused undecided)) ]
                            ) ] }

              Expect.isTrue outcome.Committed "committed"
              Expect.equal outcome.Flow [ FlowDecision.Chose false ] "the false arm"
              Expect.isEmpty outcome.Diagnostics "no diagnostic"
              Expect.equal outcome.Performed [ "ApplyOps" ] "the delete was performed"
              Expect.isFalse (world.Files.ContainsKey "notes/x.md") "the world lost the file"
          }

          test "an exit assertion that could not be evaluated halts on its own refusal, after either arm" {
              // After the TRUE arm: the assertion's refusal is reported as it
              // is, never wrapped as an assertion that did not hold.
              let afterTrue = seeded ()

              let outcome =
                  flowRun
                      afterTrue
                      { Name = "after-true"
                        Stages =
                          [ Effect(
                                ServerEffect.ApplyOps
                                    [ Branch(
                                          Exists "notes/x.md",
                                          [ Write("notes/x.md", "migrated") ],
                                          [],
                                          Some(Raises notDraft)
                                      ) ]
                            ) ] }

              Expect.isFalse outcome.Committed "halted"
              Expect.isEmpty afterTrue.Invocations "nothing performed"

              Expect.equal
                  outcome.Diagnostics
                  [ ServerDiagnostic.Failed("ApplyOps", OpRefusal.render notDraft) ]
                  "the assertion's refusal"

              // After the FALSE arm, where a refusal used to be the expected
              // answer and the effect committed.
              let afterFalse = seeded ()

              let outcome' =
                  flowRun
                      afterFalse
                      { Name = "after-false"
                        Stages =
                          [ Effect(
                                ServerEffect.ApplyOps
                                    [ Branch(Missing "notes/x.md", [], [ Delete "notes/x.md" ], Some(Raises notDraft)) ]
                            ) ] }

              Expect.isFalse outcome'.Committed "halted"
              Expect.isEmpty afterFalse.Invocations "the false arm's delete was planned, never performed"
              Expect.equal (afterFalse.Files |> Map.toList) [ "notes/x.md", "live" ] "the world is untouched"
          }

          test
              "Program's own unavailable-read refusal reaches a branch as class unavailable: it halts and takes neither arm" {
              let world = seeded ()
              let reads = Reads.Over EntryReader.live

              let outcome =
                  Handler.runWith
                      (readingWitness reads)
                      (ServerEffectRegistry.permissive ServerEffectRegistry.denyAll)
                      (OpPerformance.performedWithDetail (world.Performer None))
                      DataFrame.noResolve
                      "verb"
                      { Name = "over-the-store"
                        Stages =
                          [ Effect(
                                ServerEffect.ApplyOps
                                    [ Branch(Exists "store/index", [ Publish "origin" ], [ Delete "notes/x.md" ], None) ]
                            ) ] }
                      { Tree = { empty with Files = world.Files }
                        Bindings = () }

              let refusal =
                  "unavailable:read-unavailable: store/index (not-read: the store is unreachable)"

              Expect.equal (reads.Refusal()) (Some refusal) "the run's refusal, in the canonical form"
              Expect.isFalse outcome.Committed "halted"
              Expect.isEmpty outcome.Flow "neither arm was taken"
              Expect.isEmpty world.Invocations "nothing performed"
              Expect.isEmpty world.Published "the true arm's publish never happened"
              Expect.equal (world.Files |> Map.toList) [ "notes/x.md", "live" ] "nor the false arm's delete"
              Expect.equal outcome.Diagnostics [ ServerDiagnostic.Failed("ApplyOps", refusal) ] "on the refusal"

              Expect.equal
                  (HandlerReport.ofOutcome outcome).Diagnostics
                  [ ServerDiagnostic.Failed("ApplyOps", "unavailable:read-unavailable") ]
                  "the report names the class and the code, not the store"
          }

          test "a guard's detail does not appear in the report; a reason in no canonical form is reported as before" {
              let ambiguous = OpRefusal.refused "bundle-ambiguous" "x matches 2 bundles: x-a, x-b"

              let world = seeded ()

              let outcome =
                  run
                      world
                      None
                      { Name = "ambiguous"
                        Stages = [ Effect(ServerEffect.ApplyOps [ Check(Raises ambiguous); Publish "origin" ]) ] }

              Expect.isFalse outcome.Committed "the guard halted"
              Expect.isEmpty world.Invocations "nothing performed"

              Expect.equal
                  outcome.Diagnostics
                  [ ServerDiagnostic.Failed("ApplyOps", OpRefusal.render ambiguous) ]
                  "the host's outcome keeps the detail"

              let report = reportOf outcome
              Expect.stringContains report "\"reason\":\"refused:bundle-ambiguous\"" "the report names the refusal"
              Expect.isFalse (report.Contains "x-a") "and carries none of its detail"
              Expect.isFalse (report.Contains "matches") "none"

              // The W5 crossing in the verb's own JSON is no canonical refusal,
              // so the report carries it verbatim, as it did.
              let legacy =
                  { Code = "missing"
                    Detail = "notes/y.md" }

              let world' = seeded ()

              let outcome' =
                  run
                      world'
                      None
                      { Name = "legacy"
                        Stages = [ Effect(ServerEffect.ApplyOps [ Check(Refused legacy); Publish "origin" ]) ] }

              Expect.equal
                  (HandlerReport.ofOutcome outcome').Diagnostics
                  [ ServerDiagnostic.Failed("ApplyOps", VerbRefusal.render legacy) ]
                  "verbatim"
          }

          test "a branch over a structured refusal round-trips as a Program document" {
              let handler: VerbHandler =
                  { Name = "archive-report"
                    Stages =
                      [ Effect(
                            ServerEffect.ApplyOps
                                [ Branch(Raises notDraft, [], [ Delete "notes/x.md" ], Some(Raises notDraft)) ]
                        ) ] }

              match HandlerWire.encodeHandler witness handler with
              | Error refusal -> failtestf "did not encode: %A" refusal
              | Ok text -> Expect.equal (HandlerWire.decodeHandler witness text) (Ok handler) "back"
          } ]
