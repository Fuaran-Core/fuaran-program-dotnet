/// A performed write's receipt is its RETURN VALUE, typed (Phase 2197, D43),
/// pinned at the toy witness:
///
///   * **the receipt**: an op performer returns `OpReceipt` — the writes it
///     performed, each a target and a SHA-256 digest of the exact bytes
///     written — so a program performing two writes yields exactly two write
///     receipts naming both targets and both digests;
///   * **the union**: what an invocation changed is derived from its receipts
///     alone (`HandlerOutcome.changed`), and a commit stage accounts what it
///     would stage against them, refusing a write no receipt names, or one
///     whose content is not what the invocation wrote, as `foreign-write`;
///   * **the kinds** (Phase 2223, D65): a write is a replace, an append or a
///     delete, so an op-stream append and a file removal are receipted,
///     changed and accounted like any other write, on a fresh run and on a
///     resume, and a 0.9.0 journal's receipts still read as replaces;
///   * **the journal**: the durable tier journals each receipt, encoded, as
///     its stage's completed value, and a resumed run is SERVED the dead run's
///     receipts — the same writes, the same digests — without re-performing;
///     a journal value that is not an encoded receipt is refused, never read
///     as a receipt with no writes.
module Fuaran.Program.Tests.ReceiptTests

open Expecto
open Fuaran.Core
open Fuaran.Program.Bounded
open Fuaran.Program.Server
open Fuaran.Program.Tests.ToyDomain

// ─── fixtures ────────────────────────────────────────────────────────────────

exception private ProcessDied of string

let private crashing (f: unit -> 'T) : bool =
    try
        f () |> ignore
        false
    with ProcessDied _ ->
        true

let private leaf id label =
    { Id = id
      Label = Const(JStr label)
      Handlers = []
      Children = [] }

let private store: ServerStore<ToyNode, ToyStore> =
    { Tree =
        { Id = "root"
          Label = Const(JStr "root")
          Handlers = []
          Children = [ leaf "title" "Draft"; leaf "footer" "Plain"; leaf "commit" "-" ] }
      Bindings = Map.empty }

let private registry (audits: int ref) =
    ServerEffectRegistry.denyAll
    |> ServerEffectRegistry.register "audit" (fun _ ->
        audits.Value <- audits.Value + 1
        Ok(JStr "audited"))
    |> ServerEffectRegistry.permissive

/// Two writes, then a host call — the stage the durable tests die in front of.
let private twoWrites: Handler<ToyAction, ToyOp> =
    { Name = "two-writes"
      Stages =
        [ Effect(ServerEffect.ApplyOps [ Relabel("title", "One"); Relabel("footer", "Two") ])
          Effect(ServerEffect.HostCall("audit", JStr "after", None)) ] }

/// The performer: each relabel WRITES its label at its node's id and returns
/// the receipt of that write — the receipt IS the return value.
let private writing (performed: int ref) : OpPerformance<ToyNode, ToyOp> =
    OpPerformance.performedBy (fun _ op ->
        performed.Value <- performed.Value + 1

        match op with
        | Relabel(id, label) -> Ok(OpReceipt.ofWrites [ WriteReceipt.ofText id label ]))

let private expectedReceipts =
    [ OpReceipt.ofWrites [ WriteReceipt.ofText "title" "One" ]
      OpReceipt.ofWrites [ WriteReceipt.ofText "footer" "Two" ] ]

let private freshJournal () =
    Journal.declaringDurable (Journal.inMemory ())

let private dyingBeforeAttempting (step: int) (inner: EffectJournal) : EffectJournal =
    { inner with
        Append =
            fun entry ->
                match entry.Phase with
                | JournalPhase.Attempted when entry.Step = step -> raise (ProcessDied "between steps")
                | _ -> inner.Append entry }

let private durably journal audits performance =
    Durable.runWith
        witness
        (DurableServices.create |> DurableServices.withJournal journal)
        "inv"
        (registry audits)
        performance
        Fuaran.Compute.DataFrame.noResolve
        "node"
        twoWrites
        store

// ─── the digest ──────────────────────────────────────────────────────────────

let private digest =
    testList
        "the content digest"
        [ test "is sha256 over the UTF-8 bytes, the estate's one rendering" {
              let text = "Résumé\n"

              Expect.equal
                  (ContentDigest.ofText text).Text
                  ("sha256:" + Hash.sha256Hex text)
                  "the content address's digest"

              Expect.equal
                  (ContentDigest.ofText text)
                  (ContentDigest.ofBytes (System.Text.Encoding.UTF8.GetBytes text))
                  "text is its UTF-8 bytes, no byte-order mark"

              Expect.notEqual
                  (ContentDigest.ofText "a\n")
                  (ContentDigest.ofText "a\r\n")
                  "no newline normalisation: the bytes, not a reading of them"
          }

          test "parses only its own rendering" {
              let good = (ContentDigest.ofText "x").Text
              Expect.equal (ContentDigest.parse good) (Ok(ContentDigest.ofText "x")) "round-trips"
              Expect.isError (ContentDigest.parse (good.ToUpperInvariant())) "uppercase is refused"
              Expect.isError (ContentDigest.parse (good.Substring(0, good.Length - 1))) "an abbreviation is refused"
              Expect.isError (ContentDigest.parse ("sha1:" + good.Substring 7)) "another algorithm is refused"
          }

          test "a receipt round-trips through its journaled form, and a 0.8.0 receipt does not decode" {
              let receipt =
                  { Writes = [ WriteReceipt.ofText "a" "1"; WriteReceipt.ofBytes "b" [| 0uy; 255uy |] ]
                    Detail = JObj [ "sha", JStr "abc" ] }

              Expect.equal (OpReceipt.decode (OpReceipt.encode receipt)) (Ok receipt) "round-trips, writes in order"

              match OpReceipt.decode (JStr "receipt") with
              | Error reason ->
                  Expect.stringStarts
                      reason
                      OpReceipt.MalformedCode
                      "a bare detail is malformed, not a write-less receipt"
              | Ok _ -> failtest "a bare value decoded"

              Expect.isError
                  (OpReceipt.decode (JObj [ "writes", JArr [ JObj [ "target", JStr "a" ] ]; "detail", JObj [] ]))
                  "a write with no digest is refused"
          } ]

// ─── the receipts and the union ──────────────────────────────────────────────

let private union =
    testList
        "an invocation's changed set is the union of its receipts"
        [ test "a program performing two writes yields exactly two receipts naming both targets and digests" {
              let performed = ref 0

              let outcome =
                  Handler.runWith
                      witness
                      (registry (ref 0))
                      (writing performed)
                      Fuaran.Compute.DataFrame.noResolve
                      "node"
                      twoWrites
                      store

              Expect.isTrue outcome.Committed "committed"
              Expect.equal outcome.Receipts expectedReceipts "exactly the two receipts, in perform order"

              Expect.equal
                  (Receipts.writes outcome.Receipts |> List.map (fun w -> w.Target, w.Kind))
                  [ "title", WriteKind.Replaced(ContentDigest.ofText "One")
                    "footer", WriteKind.Replaced(ContentDigest.ofText "Two") ]
                  "each names its target and the digest of what it wrote"

              Expect.equal
                  (HandlerOutcome.changed outcome)
                  (Set.ofList [ "title"; "footer" ])
                  "the union names exactly those"
          }

          test "a write no receipt names is refused, and so is one whose content is not what was written" {
              let outcome =
                  Handler.runWith
                      witness
                      (registry (ref 0))
                      (writing (ref 0))
                      Fuaran.Compute.DataFrame.noResolve
                      "node"
                      twoWrites
                      store

              Expect.equal
                  (HandlerOutcome.account
                      outcome
                      [ WriteReceipt.ofText "title" "One"; WriteReceipt.ofText "footer" "Two" ])
                  (Ok())
                  "its own writes are accounted for"

              Expect.equal
                  (HandlerOutcome.account
                      outcome
                      [ WriteReceipt.ofText "title" "One"
                        WriteReceipt.ofText "stray" "x"
                        WriteReceipt.ofText "footer" "Tampered" ])
                  (Error
                      [ { Target = "stray"
                          Staged = [ WriteKind.Replaced(ContentDigest.ofText "x") ]
                          Cause = ForeignCause.Unreceipted }
                        { Target = "footer"
                          Staged = [ WriteKind.Replaced(ContentDigest.ofText "Tampered") ]
                          Cause = ForeignCause.Differs [ WriteKind.Replaced(ContentDigest.ofText "Two") ] } ])
                  "every foreign write, in the order staged"

              Expect.equal
                  (Receipts.final
                      [ OpReceipt.ofWrites [ WriteReceipt.ofText "t" "1" ]
                        OpReceipt.ofWrites [ WriteReceipt.ofText "t" "2" ] ]
                   |> Map.toList)
                  [ "t", [ WriteKind.Replaced(ContentDigest.ofText "2") ] ]
                  "a target written twice holds the LAST content"
          }

          test "a commit stage reads the receipts before it from its prefix and refuses a foreign write" {
              let committing (staged: WriteReceipt list) =
                  OpPerformance.performedWithPrefix (fun prefix _ op ->
                      match op with
                      | Relabel("commit", _) ->
                          match Receipts.accountAll prefix.Receipts staged with
                          | Ok() -> Ok(OpReceipt.ofDetail (JStr "committed"))
                          | Error foreign -> Error(ForeignWrite.refusal foreign)
                      | Relabel(id, label) -> Ok(OpReceipt.ofWrites [ WriteReceipt.ofText id label ]))

              let handler =
                  { Name = "write-then-commit"
                    Stages =
                      [ Effect(
                            ServerEffect.ApplyOps
                                [ Relabel("title", "One"); Relabel("footer", "Two"); Relabel("commit", "now") ]
                        ) ] }

              let run staged =
                  Handler.runWith
                      witness
                      (registry (ref 0))
                      (committing staged)
                      Fuaran.Compute.DataFrame.noResolve
                      "node"
                      handler
                      store

              let honest =
                  run [ WriteReceipt.ofText "footer" "Two"; WriteReceipt.ofText "title" "One" ]

              Expect.isTrue honest.Committed "a commit of exactly its own writes commits"

              let foreign =
                  run [ WriteReceipt.ofText "title" "One"; WriteReceipt.ofText "elsewhere" "x" ]

              Expect.isFalse foreign.Committed "a commit staging a foreign write is refused"

              Expect.equal
                  (List.tryLast foreign.Diagnostics)
                  (Some(ServerDiagnostic.PerformFailed("ApplyOps", "foreign-write: elsewhere (unreceipted)")))
                  "naming the target and the cause, never the content"

              Expect.equal
                  foreign.Receipts
                  expectedReceipts
                  "the writes that performed before the refusal are still reported"
          } ]

// ─── the kinds of write ──────────────────────────────────────────────────────

/// Two appends to one target, a delete of another, then a host call — the
/// stage the durable kinds test dies in front of (Phase 2223, D65).
let private appendsAndDelete: Handler<ToyAction, ToyOp> =
    { Name = "appends-and-delete"
      Stages =
        [ Effect(ServerEffect.ApplyOps [ Relabel("title", "+one"); Relabel("title", "+two"); Relabel("footer", "-") ])
          Effect(ServerEffect.HostCall("audit", JStr "after", None)) ] }

/// The performer: a label `+x` APPENDS `x` at its node's id, `-` DELETES it,
/// anything else replaces it — each returning the receipt of what it did.
let private writingKinds (performed: int ref) : OpPerformance<ToyNode, ToyOp> =
    OpPerformance.performedBy (fun _ op ->
        performed.Value <- performed.Value + 1

        match op with
        | Relabel(id, "-") -> Ok(OpReceipt.ofWrites [ WriteReceipt.deleted id ])
        | Relabel(id, label) when label.StartsWith "+" ->
            Ok(OpReceipt.ofWrites [ WriteReceipt.appendedText id (label.Substring 1) ])
        | Relabel(id, label) -> Ok(OpReceipt.ofWrites [ WriteReceipt.ofText id label ]))

let private kindReceipts =
    [ OpReceipt.ofWrites [ WriteReceipt.appendedText "title" "one" ]
      OpReceipt.ofWrites [ WriteReceipt.appendedText "title" "two" ]
      OpReceipt.ofWrites [ WriteReceipt.deleted "footer" ] ]

let private kinds =
    testList
        "a receipt names a replace, an append or a delete"
        [ test "two appends to one target and a delete of another are the receipts, and the changed set names both" {
              let outcome =
                  Handler.runWith
                      witness
                      (registry (ref 0))
                      (writingKinds (ref 0))
                      Fuaran.Compute.DataFrame.noResolve
                      "node"
                      appendsAndDelete
                      store

              Expect.isTrue outcome.Committed "committed"
              Expect.equal outcome.Receipts kindReceipts "each write, typed by kind, in perform order"

              Expect.equal
                  (HandlerOutcome.changed outcome)
                  (Set.ofList [ "title"; "footer" ])
                  "the appended target and the deleted one, exactly"

              Expect.equal
                  (Receipts.final outcome.Receipts |> Map.toList)
                  [ "footer", [ WriteKind.Deleted ]
                    "title",
                    [ WriteKind.Appended(ContentDigest.ofText "one")
                      WriteKind.Appended(ContentDigest.ofText "two") ] ]
                  "the delete leaves absence; the appends accumulate, in order"
          }

          test "what the invocation left is the last replace or delete and every append after it" {
              let final (writes: WriteReceipt list) =
                  Receipts.final [ OpReceipt.ofWrites writes ] |> Map.find "t"

              Expect.equal
                  (final [ WriteReceipt.ofText "t" "1"; WriteReceipt.deleted "t" ])
                  [ WriteKind.Deleted ]
                  "replaced then deleted: absent"

              Expect.equal
                  (final [ WriteReceipt.deleted "t"; WriteReceipt.ofText "t" "2" ])
                  [ WriteKind.Replaced(ContentDigest.ofText "2") ]
                  "deleted then re-created: the new content"

              Expect.equal
                  (final [ WriteReceipt.deleted "t"; WriteReceipt.appendedText "t" "a" ])
                  [ WriteKind.Deleted; WriteKind.Appended(ContentDigest.ofText "a") ]
                  "deleted then re-created by appending: from nothing, the addition"

              Expect.equal
                  (final [ WriteReceipt.ofText "t" "1"; WriteReceipt.appendedText "t" "a" ])
                  [ WriteKind.Replaced(ContentDigest.ofText "1")
                    WriteKind.Appended(ContentDigest.ofText "a") ]
                  "replaced then appended: the content, then the addition"

              Expect.equal
                  (final [ WriteReceipt.appendedText "t" "a"; WriteReceipt.ofText "t" "1" ])
                  [ WriteKind.Replaced(ContentDigest.ofText "1") ]
                  "appended then replaced: the replace supersedes the addition"
          }

          test "a commit stage's staged appends and delete are accounted, and a foreign one of each is refused" {
              Expect.equal
                  (Receipts.accountAll
                      kindReceipts
                      [ WriteReceipt.deleted "footer"
                        WriteReceipt.appendedText "title" "one"
                        WriteReceipt.appendedText "title" "two" ])
                  (Ok())
                  "the staged additions, in order, and the staged removal"

              Expect.equal
                  (Receipts.accountAll
                      kindReceipts
                      [ WriteReceipt.appendedText "title" "one"
                        WriteReceipt.appendedText "title" "two"
                        WriteReceipt.appendedText "log" "x"
                        WriteReceipt.deleted "header" ])
                  (Error
                      [ { Target = "log"
                          Staged = [ WriteKind.Appended(ContentDigest.ofText "x") ]
                          Cause = ForeignCause.Unreceipted }
                        { Target = "header"
                          Staged = [ WriteKind.Deleted ]
                          Cause = ForeignCause.Unreceipted } ])
                  "an append and a delete no receipt names"

              let appended =
                  [ WriteKind.Appended(ContentDigest.ofText "one")
                    WriteKind.Appended(ContentDigest.ofText "two") ]

              Expect.equal
                  (Receipts.accountAll
                      kindReceipts
                      [ WriteReceipt.appendedText "title" "one"
                        WriteReceipt.appendedText "title" "smuggled"
                        WriteReceipt.ofText "footer" "still here" ])
                  (Error
                      [ { Target = "title"
                          Staged =
                            [ WriteKind.Appended(ContentDigest.ofText "one")
                              WriteKind.Appended(ContentDigest.ofText "smuggled") ]
                          Cause = ForeignCause.Differs appended }
                        { Target = "footer"
                          Staged = [ WriteKind.Replaced(ContentDigest.ofText "still here") ]
                          Cause = ForeignCause.Differs [ WriteKind.Deleted ] } ])
                  "another addition, and a target receipted deleted but staged present"

              Expect.isError
                  (Receipts.accountAll kindReceipts [ WriteReceipt.appendedText "title" "one" ])
                  "staging one of two additions is not what the invocation left"

              Expect.isError
                  (Receipts.account kindReceipts (WriteReceipt.ofText "title" "onetwo"))
                  "an appended target staged as whole content is not accounted: its final content was never claimed"

              Expect.equal
                  (ForeignWrite.refusal
                      [ { Target = "footer"
                          Staged = [ WriteKind.Replaced(ContentDigest.ofText "x") ]
                          Cause = ForeignCause.Differs [ WriteKind.Deleted ] } ])
                  ("foreign-write: footer (staged "
                   + (ContentDigest.ofText "x").Text
                   + ", receipted deleted)")
                  "the refusal names both kinds, never the content"
          }

          test
              "each kind round-trips through its journaled form, a 0.9.0 write reads as a replace, and any other shape is refused" {
              let receipt =
                  { Writes =
                      [ WriteReceipt.ofText "a" "1"
                        WriteReceipt.appendedText "b" "2"
                        WriteReceipt.deleted "c" ]
                    Detail = JObj [] }

              Expect.equal (OpReceipt.decode (OpReceipt.encode receipt)) (Ok receipt) "round-trips, writes in order"

              let digest = (ContentDigest.ofText "1").Text

              Expect.equal
                  (OpReceipt.encode (OpReceipt.ofWrites [ WriteReceipt.ofText "a" "1" ]))
                  (JObj
                      [ "writes", JArr [ JObj [ "target", JStr "a"; "digest", JStr digest ] ]
                        "detail", JObj [] ])
                  "a replace is still written in the 0.9.0 form"

              let journaled090 =
                  JObj
                      [ "writes", JArr [ JObj [ "target", JStr "a"; "digest", JStr digest ] ]
                        "detail", JObj [ "sha", JStr "abc" ] ]

              Expect.equal
                  (OpReceipt.decode journaled090)
                  (Ok
                      { Writes = [ WriteReceipt.ofText "a" "1" ]
                        Detail = JObj [ "sha", JStr "abc" ] })
                  "a 0.9.0 journal's receipt, which names no kind, decodes as a replace"

              let refused (write: JVal) =
                  match OpReceipt.decode (JObj [ "writes", JArr [ write ]; "detail", JObj [] ]) with
                  | Error reason -> reason.StartsWith OpReceipt.MalformedCode
                  | Ok _ -> false

              Expect.isTrue
                  (refused (JObj [ "target", JStr "a"; "kind", JStr "truncate"; "digest", JStr digest ]))
                  "an unknown kind"

              Expect.isTrue
                  (refused (JObj [ "target", JStr "a"; "kind", JStr "replace"; "digest", JStr digest ]))
                  "a spelled-out replace is not the replace's form"

              Expect.isTrue
                  (refused (JObj [ "target", JStr "a"; "kind", JStr "delete"; "digest", JStr digest ]))
                  "a delete carrying a digest"

              Expect.isTrue (refused (JObj [ "target", JStr "a"; "kind", JStr "append" ])) "an append with no digest"
              Expect.isTrue (refused (JObj [ "target", JStr "a" ])) "a target alone is not read as a delete"
          }

          test "a resumed run is served the dead run's appends and delete, and accounts them as a fresh run does" {
              let journal = freshJournal ()
              let performed = ref 0
              let audits = ref 0

              let run (journal: EffectJournal) =
                  Durable.runWith
                      witness
                      (DurableServices.create |> DurableServices.withJournal journal)
                      "inv"
                      (registry audits)
                      (writingKinds performed)
                      Fuaran.Compute.DataFrame.noResolve
                      "node"
                      appendsAndDelete
                      store

              let died = crashing (fun () -> run (dyingBeforeAttempting 3 journal))

              Expect.isTrue died "died in front of the host call, after the three writes"
              Expect.equal performed.Value 3 "the appends and the delete performed"

              let resumed = run journal

              Expect.isTrue resumed.Outcome.Committed "committed"
              Expect.equal resumed.Replayed [ 0; 1; 2 ] "every op stage was served"
              Expect.equal performed.Value 3 "no write was performed again"
              Expect.equal resumed.Outcome.Receipts kindReceipts "the served receipts carry their kinds"

              Expect.equal
                  (HandlerOutcome.account
                      resumed.Outcome
                      [ WriteReceipt.appendedText "title" "one"
                        WriteReceipt.appendedText "title" "two"
                        WriteReceipt.deleted "footer" ])
                  (Ok())
                  "the resumed outcome accounts the staged additions and removal"
          } ]

// ─── the journal ─────────────────────────────────────────────────────────────

let private journal =
    testList
        "receipts are journaled with their stage and served on resume"
        [ test "a resumed run is served the dead run's receipts without re-performing" {
              let journal = freshJournal ()
              let performed = ref 0
              let audits = ref 0

              let died =
                  crashing (fun () -> durably (dyingBeforeAttempting 2 journal) audits (writing performed))

              Expect.isTrue died "died in front of the host call, after both writes"
              Expect.equal performed.Value 2 "both writes performed"

              let recorded =
                  journal.Read "inv"
                  |> List.choose (fun entry ->
                      match entry.Capability, entry.Phase with
                      | "ApplyOps", JournalPhase.Completed value -> Some(entry.Step, OpReceipt.decode value)
                      | _ -> None)

              Expect.equal
                  recorded
                  [ 0, Ok expectedReceipts.[0]; 1, Ok expectedReceipts.[1] ]
                  "each receipt is journaled, typed, at its stage's ordinal"

              let resumed = durably journal audits (writing performed)

              Expect.isTrue resumed.Outcome.Committed "committed"
              Expect.equal resumed.Replayed [ 0; 1 ] "both op stages were served"
              Expect.equal performed.Value 2 "neither write was performed again"
              Expect.equal audits.Value 1 "the host call ran once"
              Expect.equal resumed.Outcome.Receipts expectedReceipts "the served receipts ARE the run's receipts"

              Expect.equal
                  (HandlerOutcome.changed resumed.Outcome)
                  (Set.ofList [ "title"; "footer" ])
                  "the union on a resume is the union of a fresh run"
          }

          test "a journaled op stage that is not an encoded receipt is refused on resume, never read as no writes" {
              let journal = freshJournal ()
              let subject = Durable.opSubject witness.State (Relabel("title", "One"))

              for phase in [ JournalPhase.Attempted; JournalPhase.Completed(JStr "a 0.8.0 receipt") ] do
                  journal.Append
                      { Invocation = "inv"
                        Step = 0
                        Capability = "ApplyOps"
                        Subject = Some subject
                        Phase = phase }

              let performed = ref 0
              let resumed = durably journal (ref 0) (writing performed)

              Expect.isFalse resumed.Outcome.Committed "refused"
              Expect.equal performed.Value 0 "the served stage was not re-performed to paper over it"

              match List.tryLast resumed.Outcome.Diagnostics with
              | Some(ServerDiagnostic.PerformFailed("ApplyOps", reason)) ->
                  Expect.stringStarts reason OpReceipt.MalformedCode "named as a malformed receipt"
              | other -> failtestf "expected a PerformFailed naming the malformed receipt, got %A" other
          } ]

// ─── a part-way failure (Phase 2224, D68) ────────────────────────────────────
//
// One op, three files: a relabel writes `<id>`, `<id>.index` and `<id>.log`. The
// performer for the SECOND op writes the first two and fails — the loss the
// plane probe found: under a string-only refusal, nothing Program returned said
// those two files were on disk.

let private threeFiles (id: string) (label: string) =
    [ WriteReceipt.ofText id label
      WriteReceipt.ofText (id + ".index") label
      WriteReceipt.ofText (id + ".log") label ]

let private titleReceipt = OpReceipt.ofWrites (threeFiles "title" "One")

/// What the footer's performer had written when it gave up: two of three.
let private footerPartial =
    OpReceipt.ofWrites (threeFiles "footer" "Two" |> List.take 2)

let private DiskFull = "disk full at the log"

/// Writes all three files for the title; two for the footer, then fails WITH the
/// partial.
let private failingPartWay (performed: int ref) : OpPerformance<ToyNode, ToyOp> =
    OpPerformance.performedWithFailure (fun _ _ op ->
        performed.Value <- performed.Value + 1

        match op with
        | Relabel("footer", _) -> Error(OpFailure.partial DiskFull footerPartial)
        | Relabel(id, label) -> Ok(OpReceipt.ofWrites (threeFiles id label)))

/// The same, refusing the footer with a reason alone — the plain registration.
let private failingPlainly (performed: int ref) : OpPerformance<ToyNode, ToyOp> =
    OpPerformance.performedBy (fun _ op ->
        performed.Value <- performed.Value + 1

        match op with
        | Relabel("footer", _) -> Error "declined"
        | Relabel(id, label) -> Ok(OpReceipt.ofWrites (threeFiles id label)))

/// Dies INSIDE the footer's performer, after writing — the process never
/// returns, so no receipt, partial or whole, is ever answered.
let private dyingPartWay (performed: int ref) : OpPerformance<ToyNode, ToyOp> =
    OpPerformance.performedWithFailure (fun _ _ op ->
        performed.Value <- performed.Value + 1

        match op with
        | Relabel("footer", _) -> raise (ProcessDied "inside the stage")
        | Relabel(id, label) -> Ok(OpReceipt.ofWrites (threeFiles id label)))

let private directly performance =
    Handler.runWith witness (registry (ref 0)) performance Fuaran.Compute.DataFrame.noResolve "node" twoWrites store

let private lastDiagnostic (outcome: HandlerOutcome<ToyNode, ToyStore, ToyOp, ToyEffect>) =
    List.tryLast outcome.Diagnostics

let private refusedOpStages (journal: EffectJournal) =
    journal.Read "inv"
    |> List.choose (fun entry ->
        match entry.Capability, entry.Phase with
        | "ApplyOps", JournalPhase.Refused(reason, partial) -> Some(entry.Step, reason, partial)
        | _ -> None)

let private partial =
    testList
        "an op stage that fails part-way keeps the receipts of the effects it did perform"
        [ test
              "a performer that writes two of three files and fails yields an outcome whose receipts name exactly those two" {
              let outcome = directly (failingPartWay (ref 0))

              Expect.isFalse outcome.Committed "rolled back"

              Expect.equal
                  (lastDiagnostic outcome)
                  (Some(ServerDiagnostic.PerformFailed("ApplyOps", DiskFull)))
                  "the diagnostic keeps its shape: the capability and the performer's reason"

              Expect.equal
                  outcome.Receipts
                  [ titleReceipt; footerPartial ]
                  "the completed stage's receipt, then the failing stage's partial — every effect performed"

              Expect.equal
                  outcome.Performed
                  [ "ApplyOps" ]
                  "Performed is still the stage-granular prefix: the failing stage is not in it"

              Expect.equal
                  (HandlerOutcome.changed outcome)
                  (Set.ofList [ "title"; "title.index"; "title.log"; "footer"; "footer.index" ])
                  "changed names the two files the failing stage wrote and not the one it did not"
          }

          test "a plain Error still reports an empty partial, and the outcome's receipts are the stages before it" {
              let outcome = directly (failingPlainly (ref 0))

              Expect.equal (OpFailure.plain "declined").Performed OpReceipt.none "a plain failure performed nothing"
              Expect.isFalse outcome.Committed "rolled back"

              Expect.equal
                  (lastDiagnostic outcome)
                  (Some(ServerDiagnostic.PerformFailed("ApplyOps", "declined")))
                  "the reason"

              Expect.equal outcome.Receipts [ titleReceipt ] "nothing is appended for a failure that performed nothing"

              Expect.equal
                  (HandlerOutcome.changed outcome)
                  (Set.ofList [ "title"; "title.index"; "title.log" ])
                  "changed is the completed stage's alone"
          }

          test
              "a receipt a contract rejects is not a partial: the refusal names the contract and performs nothing on the record" {
              let rejectingFooter: OpContract<ToyNode, ToyOp> =
                  OpContract.at "footer-forbidden" (fun _ op _ ->
                      match op with
                      | Relabel(id, _) -> id <> "footer")

              let completing: OpPerformance<ToyNode, ToyOp> =
                  OpPerformance.performedWithFailure (
                      OpContract.checkAll [ rejectingFooter ] (fun _ _ op ->
                          match op with
                          | Relabel(id, label) -> Ok(OpReceipt.ofWrites (threeFiles id label)))
                  )

              let outcome = directly completing

              Expect.isFalse outcome.Committed "rolled back"

              Expect.equal
                  (lastDiagnostic outcome)
                  (Some(ServerDiagnostic.PerformFailed("ApplyOps", "return-contract:footer-forbidden")))
                  "the contract's name"

              Expect.equal outcome.Receipts [ titleReceipt ] "the rejected receipt's writes are not in the record"
          }

          test
              "a durable run that refused part-way is served the same partial receipts on resume, without re-performing" {
              let journal = freshJournal ()
              let performed = ref 0
              let audits = ref 0

              let first = durably journal audits (failingPartWay performed)

              Expect.isFalse first.Outcome.Committed "refused on the fresh run"

              Expect.equal
                  first.Outcome.Receipts
                  [ titleReceipt; footerPartial ]
                  "the fresh run's receipts are per effect"

              Expect.equal performed.Value 2 "both stages were invoked once"

              Expect.equal
                  (refusedOpStages journal)
                  [ 1, DiskFull, Some(OpReceipt.encode footerPartial) ]
                  "the refusal is journaled at the stage's ordinal with its partial receipt, encoded as a completed one is"

              let resumed = durably journal audits (failingPartWay performed)

              Expect.isFalse resumed.Outcome.Committed "the served refusal refuses the resume too"
              Expect.equal resumed.Replayed [ 0; 1 ] "both op stages were served"
              Expect.equal performed.Value 2 "neither stage was performed again"
              Expect.equal audits.Value 0 "the host call after the failing stage never ran"

              Expect.equal
                  (lastDiagnostic resumed.Outcome)
                  (Some(ServerDiagnostic.PerformFailed("ApplyOps", DiskFull)))
                  "the dead run's reason"

              Expect.equal
                  resumed.Outcome.Receipts
                  [ titleReceipt; footerPartial ]
                  "the served partial IS the resumed run's partial"

              Expect.equal
                  (HandlerOutcome.changed resumed.Outcome)
                  (HandlerOutcome.changed first.Outcome)
                  "the union on a resume is the union of the fresh run"
          }

          test "a plain refusal is journaled with no partial" {
              let journal = freshJournal ()
              durably journal (ref 0) (failingPlainly (ref 0)) |> ignore
              Expect.equal (refusedOpStages journal) [ 1, "declined", None ] "reason alone"
          }

          test
              "a death inside a stage stays indeterminate: no partial is known to the journal, and the resume is refused (D23)" {
              let journal = freshJournal ()
              let performed = ref 0

              let died = crashing (fun () -> durably journal (ref 0) (dyingPartWay performed))

              Expect.isTrue died "died inside the footer's performer"
              Expect.equal (refusedOpStages journal) [] "nothing was refused: the performer never returned"

              let resumed = durably journal (ref 0) (dyingPartWay performed)

              Expect.isFalse resumed.Outcome.Committed "refused"
              Expect.equal resumed.Indeterminate [ 1 ] "the footer's stage is the indeterminate one"
              Expect.equal performed.Value 2 "not re-invoked to find out"

              Expect.equal
                  (lastDiagnostic resumed.Outcome)
                  (Some(ServerDiagnostic.PerformFailed("ApplyOps", DurableCode.IndeterminateStep)))
                  "named indeterminate, not served a partial it cannot know"

              Expect.equal resumed.Outcome.Receipts [ titleReceipt ] "the receipts stop at the last stage that returned"
          }

          test "a served partial that is not an encoded receipt is refused as malformed, never read as no writes" {
              let journal = freshJournal ()
              let subject = Durable.opSubject witness.State (Relabel("title", "One"))

              for phase in
                  [ JournalPhase.Attempted
                    JournalPhase.Refused("gave up", Some(JStr "a receipt from before receipts were typed")) ] do
                  journal.Append
                      { Invocation = "inv"
                        Step = 0
                        Capability = "ApplyOps"
                        Subject = Some subject
                        Phase = phase }

              let performed = ref 0
              let resumed = durably journal (ref 0) (failingPartWay performed)

              Expect.isFalse resumed.Outcome.Committed "refused"
              Expect.equal performed.Value 0 "the served stage was not re-performed"
              Expect.isEmpty resumed.Outcome.Receipts "nothing was read as a partial"

              match lastDiagnostic resumed.Outcome with
              | Some(ServerDiagnostic.PerformFailed("ApplyOps", reason)) ->
                  Expect.stringStarts reason OpReceipt.MalformedCode "the journal's defect is the reason"
              | other -> failtestf "expected a PerformFailed naming the malformed partial, got %A" other
          } ]

[<Tests>]
let receiptTests =
    testList "Phase 2197 - a performed write's receipt is its return value" [ digest; union; kinds; journal; partial ]
