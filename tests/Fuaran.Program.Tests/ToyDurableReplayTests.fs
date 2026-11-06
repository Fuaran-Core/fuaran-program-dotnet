/// The proved durable replay as oracle, at the TOY witness (fuaran#2017).
///
/// `proofs/Staging.fst` models `Durable.runWith`'s perform phase — `decide`
/// and `replay` over a journal SNAPSHOT — and its extraction (`proofs/oracle`)
/// runs here beside production over every journal shape a crash can leave
/// behind: nothing recorded, interrupted between two op stages, a crash inside
/// the second op stage under each of the three policies, a host call refusing
/// on the resume, a recorded refusal served, and a recorded ordinal holding
/// another op. Phase 1980 first certified this through the UI tier only; a
/// claim about the generic durable interpreter that is evidenced at one
/// domain's types alone has not been shown of the generic interpreter, so the
/// same differential is hosted here, at the toy's own node, op and store.
///
/// The staged list is built by hand in the shape the plan phase stages for
/// `editsThenAudit`: two `Relabel` op stages carrying their subjects, one host
/// call. The snapshot is read from the production journal's own entries
/// through `stepOf`, `capabilityOf` and `subjectOf`, so the model and
/// production read the same bytes.
///
/// A comparison that has never been seen to lose is not evidence, so the
/// differential REPORTS its mismatches rather than asserting them, and the
/// GO RED cases at the foot of the list make production and the model
/// disagree — a model fed the wrong subject, a mis-stated journal, a
/// mis-stated policy — and require the differential to say so.
module Fuaran.Program.Tests.ToyDurableReplayTests

open Expecto
open Fuaran.Core
open Fuaran.Program.Server
open Fuaran.Program.Tests.ToyDomain

// ─── fixtures ────────────────────────────────────────────────────────────────

/// A counting host performer: the number of times the host actually ran it.
type private Counter() =
    let mutable count = 0
    member _.Count = count
    member _.Bump() = count <- count + 1

let private counting (counter: Counter) (answer: string) =
    fun (_: JVal) ->
        counter.Bump()
        Ok(JStr answer)

/// The process dying. Raised from inside a performer or a journal append, so
/// the run is cut exactly where a real crash would cut it.
exception internal ProcessDied of string

/// Run something that is expected to die, and report whether it did. A crash
/// the fixture did not observe would make every assertion after it a test of
/// some other journal shape.
let internal crashing (f: unit -> 'T) : bool =
    try
        f () |> ignore
        false
    with ProcessDied _ ->
        true

/// The tree the handler runs against: the two nodes the op stages relabel,
/// with literal labels, so each `Relabel` applies rather than addressing a
/// node that is not there.
let internal baseTree: ToyNode =
    let leaf id label =
        { Id = id
          Label = Const(JStr label)
          Handlers = []
          Children = [] }

    { Id = "root"
      Label = Const(JStr "root")
      Handlers = []
      Children = [ leaf "title" "Draft"; leaf "footer" "Plain" ] }

let internal emptyStore: ServerStore<ToyNode, ToyStore> =
    { Tree = baseTree
      Bindings = Map.empty }

let internal registryOf (performers: (string * (JVal -> Result<JVal, string>)) list) =
    performers
    |> List.fold (fun r (fn, p) -> ServerEffectRegistry.register fn p r) ServerEffectRegistry.denyAll
    |> ServerEffectRegistry.permissive

let private relabelTitle = Relabel("title", "Edited")
let private relabelFooter = Relabel("footer", "Edited")

/// An op, as this suite compares it: its canonical form off the state axis.
let private enc (op: ToyOp) = witness.State.Stream.Encode op

/// The journal subject of an op — what production records for its stage.
let private subjectOf (op: ToyOp) = Durable.opSubject witness.State op

/// Two ops in one stage and a host call after them, so under a registered op
/// performer the staged list is op, op, host call — three ordinals in ONE
/// sequence, which is the shape the certification needs.
let private editsThenAudit: Handler<ToyAction, ToyOp> =
    { Name = "edits"
      Stages =
        [ Effect(ServerEffect.ApplyOps [ relabelTitle; relabelFooter ])
          Effect(ServerEffect.HostCall("audit", JStr "edited", None)) ] }

/// The same ops in the other order: the same capability at every ordinal and
/// different subjects, which only the subject can tell apart.
let private editsSwapped: Handler<ToyAction, ToyOp> =
    { Name = "edits-swapped"
      Stages =
        [ Effect(ServerEffect.ApplyOps [ relabelFooter; relabelTitle ])
          Effect(ServerEffect.HostCall("audit", JStr "edited", None)) ] }

/// What an op performer was handed, in order.
type private OpLog() =
    let performed = ResizeArray<string>()
    member _.Performed = List.ofSeq performed
    member _.Record(op: ToyOp) = performed.Add(enc op)

/// An op performer that records and succeeds.
let private performing (log: OpLog) : OpPerformance<ToyNode, ToyOp> =
    OpPerformance.performedWithoutReceipt (fun _ op ->
        log.Record op
        Ok())

/// An op performer that performs the relabel of `victim` and then the process
/// dies — the crash inside the indeterminate window, where the effect happened
/// and the record of it did not.
let private performingThenDyingAt (victim: string) (log: OpLog) : OpPerformance<ToyNode, ToyOp> =
    OpPerformance.performedWithoutReceipt (fun _ op ->
        log.Record op

        match op with
        | Relabel(id, _) when id = victim -> raise (ProcessDied "after the op")
        | _ -> Ok())

/// A journal the process dies in front of: the ATTEMPT record for `step` kills
/// the process before it lands — the interruption BETWEEN two steps, the one
/// before completed and recorded and the next never attempted.
let internal dyingBeforeAttempting (step: int) (inner: EffectJournal) : EffectJournal =
    { inner with
        Append =
            fun entry ->
                match entry.Phase with
                | JournalPhase.Attempted when entry.Step = step -> raise (ProcessDied "between steps")
                | _ -> inner.Append entry }

let private auditRegistry (audit: Counter) =
    registryOf [ "audit", counting audit "recorded" ]

let private runEdits
    (services: DurableServices)
    (registry: ServerEffectRegistry)
    (performance: OpPerformance<ToyNode, ToyOp>)
    (handler: Handler<ToyAction, ToyOp>)
    =
    Durable.runWith
        witness
        services
        "inv"
        registry
        performance
        Fuaran.Compute.DataFrame.noResolve
        "node"
        handler
        emptyStore

let internal freshJournal () =
    Journal.declaringDurable (Journal.inMemory ())

// ─── the model's side ────────────────────────────────────────────────────────

/// The model's performer token for this host: production's closure, with the
/// subject and the declaration the model's arrows read off it.
type private Token =
    { Subject: string option
      Idempotent: bool
      Invoke: JVal -> Result<JVal, string> }

let private modelOpt (value: 'T option) : Staging.opt<'T> =
    match value with
    | Some v -> Staging.OSome v
    | None -> Staging.ONone

let private modelRes (value: Result<'T, string>) : Staging.res<'T> =
    match value with
    | Ok v -> Staging.ROk v
    | Error e -> Staging.RErr e

/// Only `w_assign` is reachable — no staged call here lands a slot — and the
/// rest refuse loudly: the replay differential is about the perform phase and
/// stages no plan, so a model that reached one would be modelling something
/// else.
let private modelWitness: Staging.witness<ToyNode, ToyStore, JVal, ToyOp, obj, obj, obj, obj> =
    { w_compute = fun _ _ _ -> failwith "the replay differential plans nothing"
      w_undo_compute = fun _ _ _ -> failwith "the replay differential plans nothing"
      w_query = fun _ _ _ -> failwith "the replay differential plans nothing"
      w_apply = fun _ _ -> failwith "the replay differential plans nothing"
      w_op_view = fun _ -> failwith "the replay differential plans nothing"
      w_read_extent = fun _ _ -> failwith "the replay differential plans nothing"
      w_resolve = fun _ _ -> failwith "the replay differential plans nothing"
      w_assign = fun _ _ bindings -> bindings
      w_land_query = fun _ _ bindings -> bindings
      w_slot_refused = fun _ -> failwith "the replay differential plans nothing" }

let private modelRegistry: Staging.registry<ToyNode, JVal, ToyOp, obj, Token> =
    { r_gate = fun _ -> true
      r_policy = fun _ -> Staging.ONone
      r_lookup = fun _ -> Staging.ONone
      r_perf = fun token args -> token.Invoke args |> modelRes
      r_op_perform = Staging.ONone
      r_query_posture = Staging.PureRead
      r_query_stage = fun _ _ -> failwith "the replay differential plans nothing"
      r_record = fun _ -> failwith "the replay differential plans nothing" }

/// The journal snapshot as the model reads it, from the production journal's
/// own entries: `stepOf` for the three-state reading, `capabilityOf` and
/// `subjectOf` for the recorded identity.
let private modelJournal (entries: JournalEntry list) : Staging.journal<JVal> =
    { j_step =
        fun k ->
            match Journal.stepOf entries (int k) with
            | JournaledStep.Unrun -> Staging.JUnrun
            | JournaledStep.Value v -> Staging.JValue v
            | JournaledStep.Refusal r -> Staging.JRefusal r
            | JournaledStep.Indeterminate _ -> Staging.JIndeterminate
      j_recorded =
        fun k ->
            match Journal.capabilityOf entries (int k), Journal.subjectOf entries (int k) with
            | Some capability, Some subject -> Staging.OSome(capability, modelOpt subject)
            | _ -> Staging.ONone }

/// The staged list the plan phase stages for `editsThenAudit` under a
/// registered op performer, with the resume's performers as tokens. `ops` is
/// the two op stages' ops in plan order — a parameter so a GO RED case can
/// feed the model the wrong subjects.
let private modelStaged
    (ops: ToyOp list)
    (opDeclared: bool)
    (auditDeclared: bool)
    (audit: JVal -> Result<JVal, string>)
    : Staging.staged_call<JVal, Token> list =
    let opStage (op: ToyOp) : Staging.staged_call<JVal, Token> =
        { Staging.sc_capability = Durable.OpStageCapability
          Staging.sc_performer =
            { Subject = Some(subjectOf op)
              Idempotent = opDeclared
              Invoke = fun _ -> Ok(JObj []) }
          Staging.sc_args = JObj []
          Staging.sc_into = Staging.LNowhere }

    let hostCall: Staging.staged_call<JVal, Token> =
        { Staging.sc_capability = "host:audit"
          Staging.sc_performer =
            { Subject = None
              Idempotent = auditDeclared
              Invoke = audit }
          Staging.sc_args = JStr "edited"
          Staging.sc_into = Staging.LNowhere }

    (ops |> List.map opStage) @ [ hostCall ]

let private modelDiagnostic (diagnostic: Staging.diagnostic<obj>) : ServerDiagnostic =
    match diagnostic with
    | Staging.PerformFailed(capability, reason) -> ServerDiagnostic.PerformFailed(capability, reason)
    | Staging.Failed(capability, reason) -> ServerDiagnostic.Failed(capability, reason)
    | Staging.Denied(Staging.Unregistered capability) ->
        ServerDiagnostic.Denied(ServerEffectDenial.Unregistered capability)
    | Staging.Denied(Staging.GateRefused capability) ->
        ServerDiagnostic.Denied(ServerEffectDenial.GateRefused capability)
    | Staging.Bounded _ -> failwith "the replay differential plans nothing"

// ─── the differential ────────────────────────────────────────────────────────

/// How a GO RED case makes the model's side disagree with production's. The
/// honest differential uses `faithful`; every other value mis-states ONE
/// thing the model is handed, and the differential must notice.
type private Bend =
    { ModelOps: ToyOp list
      ModelEntries: JournalEntry list -> JournalEntry list
      ModelReinvoke: bool -> bool }

let private faithful: Bend =
    { ModelOps = [ relabelTitle; relabelFooter ]
      ModelEntries = id
      ModelReinvoke = id }

/// One comparison's result: production's outcome, what the resume's op
/// performer was handed, and the name of every compared thing on which the
/// model and production DISAGREED, with both sides printed.
type private Differential =
    { Production: DurableOutcome<ToyNode, ToyStore, ToyOp, ToyEffect>
      ResumeLog: OpLog
      Mismatches: (string * string) list }

/// One differential: production's resume over `journal` under `services`,
/// against the model's `replay` over the same snapshot, the same staged shape
/// and the same performer verdicts. Seven things are compared: the four
/// ordinal lists, the verdict, the audit trail and the diagnostics.
let private replayDifferentialBent
    (bend: Bend)
    (services: DurableServices)
    (journal: EffectJournal)
    (auditAnswer: JVal -> Result<JVal, string>)
    : Differential =
    let snapshot = journal.Read "inv"
    let resumeLog = OpLog()

    let production =
        runEdits
            (services |> DurableServices.withJournal journal)
            (registryOf [ "audit", auditAnswer ])
            (performing resumeLog)
            editsThenAudit

    let dur: Staging.durable<JVal, Token> =
        { d_journal = modelJournal (bend.ModelEntries snapshot)
          d_subject = fun call -> modelOpt call.sc_performer.Subject
          d_idempotent = fun call -> call.sc_performer.Idempotent
          d_reinvoke = bend.ModelReinvoke services.ReinvokeIndeterminate }

    let staged =
        modelStaged
            bend.ModelOps
            (PerformerFacets.opPerformerFacet services.Performers = IdempotencyFacet.Idempotent)
            (PerformerFacets.facetOf "audit" services.Performers = IdempotencyFacet.Idempotent)
            auditAnswer

    let model =
        Staging.replay
            modelWitness
            modelRegistry
            dur
            0I
            staged
            (Staging.start
                { st_tree = baseTree
                  st_bindings = Map.empty })

    let ordinals (xs: bigint list) = xs |> List.map int

    let compare name (productionSide: 'T) (modelSide: 'T) =
        if productionSide = modelSide then
            None
        else
            Some(name, sprintf "production %A, model %A" productionSide modelSide)

    let mismatches =
        [ compare "replayed" production.Replayed (ordinals model.rp_replayed)
          compare "invoked" production.Invoked (ordinals model.rp_invoked)
          compare "indeterminate" production.Indeterminate (ordinals model.rp_indeterminate)
          compare "overrides" (production.Overrides |> List.map _.Step) (ordinals model.rp_overrides)
          compare "verdict" production.Outcome.Committed (not model.rp_acc.ac_halted)
          // Served stages included, because the outcome is recomputed.
          compare "audit trail" production.Outcome.Performed (Staging.rev model.rp_acc.ac_externally)
          compare
              "diagnostics"
              production.Outcome.Diagnostics
              (Staging.rev model.rp_acc.ac_diagnostics |> List.map modelDiagnostic) ]
        |> List.choose id

    { Production = production
      ResumeLog = resumeLog
      Mismatches = mismatches }

/// The honest differential, asserted: the model and production agree on all
/// seven, and a disagreement names what diverged and both values.
let private replayDifferential services journal auditAnswer =
    let result = replayDifferentialBent faithful services journal auditAnswer

    Expect.isEmpty result.Mismatches (sprintf "the extracted replay and Durable.runWith disagree: %A" result.Mismatches)

    result

// ─── the journal shapes ──────────────────────────────────────────────────────

/// A first run's journal: nothing recorded.
let private nothingRecorded () = freshJournal ()

/// The process died between the first op stage's record and the second's
/// attempt.
let private interruptedBetweenOps () =
    let journal = freshJournal ()

    let died =
        crashing (fun () ->
            runEdits
                (DurableServices.create
                 |> DurableServices.withJournal (dyingBeforeAttempting 1 journal))
                (auditRegistry (Counter()))
                (performing (OpLog()))
                editsThenAudit)

    Expect.isTrue died "the fixture's process died between the two op stages"
    journal

/// A completed run whose host call refused: three decided steps, the last a
/// refusal.
let private recordedRefusal () =
    let journal = freshJournal ()

    runEdits
        (DurableServices.create |> DurableServices.withJournal journal)
        (registryOf [ "audit", (fun _ -> Error "refused") ])
        (performing (OpLog()))
        editsThenAudit
    |> ignore

    journal

/// The process died inside the second op performer, after its effect: one op
/// stage decided, one attempted.
let private crashedInsideSecondOp (services: DurableServices) () =
    let journal = freshJournal ()

    let died =
        crashing (fun () ->
            runEdits
                (services |> DurableServices.withJournal journal)
                (auditRegistry (Counter()))
                (performingThenDyingAt "footer" (OpLog()))
                editsThenAudit)

    Expect.isTrue died "the fixture's process died inside the second op performer"
    journal

/// A completed run of the SWAPPED handler: every ordinal recorded, ordinal 0
/// holding the footer's relabel where the resumed handler holds the title's.
let private recordedOtherOp () =
    let journal = freshJournal ()

    runEdits
        (DurableServices.create |> DurableServices.withJournal journal)
        (auditRegistry (Counter()))
        (performing (OpLog()))
        editsSwapped
    |> ignore

    journal

/// A completed run of the handler itself: every ordinal recorded as served.
let private completedRun () =
    let journal = freshJournal ()

    runEdits
        (DurableServices.create |> DurableServices.withJournal journal)
        (auditRegistry (Counter()))
        (performing (OpLog()))
        editsThenAudit
    |> ignore

    journal

let private recorded (_: JVal) = Ok(JStr "recorded")

let private policies =
    [ "strict", DurableServices.create
      "accepting", DurableServices.create |> DurableServices.acceptingIndeterminateReplay
      "declared idempotent",
      DurableServices.create
      |> DurableServices.declaringOpPerformer IdempotencyFacet.Idempotent ]

/// Every agreement case as data — name, services, journal, the resume's host
/// answer, and what production must have done for the case to be the shape it
/// names — so the shape test below can re-run them all and check the corpus
/// reaches every journal shape it claims to.
type private Case =
    { Name: string
      Services: DurableServices
      Journal: unit -> EffectJournal
      Audit: JVal -> Result<JVal, string>
      Shape: Differential -> unit }

let private cases: Case list =
    [ { Name = "a first run: nothing recorded, everything invoked"
        Services = DurableServices.create
        Journal = nothingRecorded
        Audit = recorded
        Shape =
          fun d ->
              Expect.equal d.Production.Invoked [ 0; 1; 2 ] "every ordinal invoked"
              Expect.equal d.ResumeLog.Performed [ enc relabelTitle; enc relabelFooter ] "both ops performed" }

      { Name = "interrupted between two op stages: the prefix served, the rest performed"
        Services = DurableServices.create
        Journal = interruptedBetweenOps
        Audit = recorded
        Shape =
          fun d ->
              Expect.equal d.Production.Replayed [ 0 ] "the differential ran the resume case"
              Expect.equal d.ResumeLog.Performed [ enc relabelFooter ] "only the op after the recorded prefix" }

      { Name = "interrupted, and the host call refuses on the resume"
        Services = DurableServices.create
        Journal = interruptedBetweenOps
        Audit = fun _ -> Error "refused"
        Shape =
          fun d ->
              Expect.isFalse d.Production.Outcome.Committed "the differential ran the refusal case"
              Expect.equal d.Production.Invoked [ 1; 2 ] "and the refused call counts as invoked" }

      { Name = "a recorded refusal is served, and halts where it halted"
        Services = DurableServices.create
        Journal = recordedRefusal
        Audit = recorded
        Shape =
          fun d ->
              Expect.equal d.Production.Replayed [ 0; 1; 2 ] "every step served, the refusal included"
              Expect.isFalse d.Production.Outcome.Committed "and the served refusal halts"
              Expect.equal d.ResumeLog.Performed [] "and no op performed" } ]
    @ [ for name, services in policies ->
            { Name = sprintf "a crash inside the second op stage, under each policy: %s" name
              Services = services
              Journal = crashedInsideSecondOp services
              Audit = recorded
              Shape =
                fun d ->
                    Expect.equal d.Production.Replayed [ 0 ] "the differential ran the indeterminate case"

                    // Which way the policy took the undecided step is the
                    // case's whole point: strict refuses it, the other two
                    // re-invoke it, and only the opt-in records an override.
                    if services.ReinvokeIndeterminate then
                        Expect.equal (d.Production.Overrides |> List.map _.Step) [ 1 ] "overridden and recorded"
                    elif name = "strict" then
                        Expect.equal d.Production.Indeterminate [ 1 ] "refused undecided"
                    else
                        Expect.equal d.Production.Invoked [ 1; 2 ] "re-invoked with no override"
                        Expect.equal d.Production.Overrides [] "the declared shape closes the window" } ]
    @ [ { Name = "a recorded ordinal holding another op: refused as divergence"
          Services = DurableServices.create
          Journal = recordedOtherOp
          Audit = recorded
          Shape =
            fun d ->
                Expect.equal
                    d.Production.Outcome.Diagnostics
                    [ ServerDiagnostic.PerformFailed(Durable.OpStageCapability, DurableCode.ReplayDivergence) ]
                    "the differential ran the divergence case" } ]

let private runCase (case: Case) =
    replayDifferential case.Services (case.Journal()) case.Audit

[<Tests>]
let tests =
    testList
        "Phase 1980 - the proved durable replay as oracle at the toy witness"
        [ yield!
              cases
              |> List.map (fun case ->
                  test case.Name {
                      let d = runCase case
                      case.Shape d
                  })

          test "the cases reach every journal shape the claim names, and no fewer cases than the UI host" {
              // The UI host runs eight; the toy re-hosts every one of them.
              Expect.isGreaterThanOrEqual (List.length cases) 8 "the case floor"

              let outcomes = cases |> List.map (fun c -> (runCase c).Production)

              let reached what (holds: DurableOutcome<_, _, _, _> -> bool) =
                  Expect.isTrue (outcomes |> List.exists holds) (sprintf "no case reaches %s" what)

              reached "a run with nothing served" (fun o -> o.Replayed = [] && o.Invoked = [ 0; 1; 2 ])
              reached "a served prefix" (fun o -> o.Replayed = [ 0 ] && o.Invoked <> [])
              reached "an indeterminate refusal" (fun o -> o.Indeterminate <> [])
              reached "a recorded override" (fun o -> o.Overrides <> [])
              reached "a served refusal" (fun o -> o.Replayed = [ 0; 1; 2 ] && not o.Outcome.Committed)

              reached "a host call refusing on the resume" (fun o ->
                  o.Outcome.Diagnostics = [ ServerDiagnostic.PerformFailed("host:audit", "refused") ]
                  && o.Invoked = [ 1; 2 ])

              reached "a divergence" (fun o ->
                  o.Outcome.Diagnostics
                  |> List.contains (
                      ServerDiagnostic.PerformFailed(Durable.OpStageCapability, DurableCode.ReplayDivergence)
                  ))
          }

          testList
              "GO RED - the differential loses when production and the model disagree"
              [ test "a model fed the wrong subject at a recorded ordinal" {
                    // The journal is a completed run of the handler itself, so
                    // production serves every step. The model is handed the
                    // two ops in the swapped order: its identity at ordinal 0
                    // is the footer's relabel, the journal's the title's.
                    let d =
                        replayDifferentialBent
                            { faithful with
                                ModelOps = [ relabelFooter; relabelTitle ] }
                            DurableServices.create
                            (completedRun ())
                            recorded

                    Expect.equal d.Production.Replayed [ 0; 1; 2 ] "production served every step"

                    let lost = d.Mismatches |> List.map fst
                    Expect.contains lost "replayed" "the differential saw the model refuse what production served"
                    Expect.contains lost "verdict" "and the verdicts part"
                    Expect.contains lost "diagnostics" "and the model's divergence diagnostic"
                }

                test "a mis-stated journal: the recorded completion withheld from the model" {
                    // Production reads the journal after an interruption
                    // between the op stages and serves ordinal 0. The model is
                    // handed the snapshot without ordinal 0's completion, so
                    // it reads the step as attempted and undecided.
                    let d =
                        replayDifferentialBent
                            { faithful with
                                ModelEntries =
                                    List.filter (fun e ->
                                        not (
                                            e.Step = 0
                                            && (match e.Phase with
                                                | JournalPhase.Completed _ -> true
                                                | _ -> false)
                                        )) }
                            DurableServices.create
                            (interruptedBetweenOps ())
                            recorded

                    let lost = d.Mismatches |> List.map fst
                    Expect.contains lost "replayed" "production served ordinal 0 and the model did not"
                    Expect.contains lost "indeterminate" "the model refused it undecided"
                    Expect.contains lost "verdict" "so the verdicts part"
                }

                test "a mis-stated policy: the model refuses what production was told to re-invoke" {
                    let accepting =
                        DurableServices.create |> DurableServices.acceptingIndeterminateReplay

                    let d =
                        replayDifferentialBent
                            { faithful with
                                ModelReinvoke = fun _ -> false }
                            accepting
                            (crashedInsideSecondOp accepting ())
                            recorded

                    let lost = d.Mismatches |> List.map fst
                    Expect.contains lost "overrides" "production recorded an override the model never took"
                    Expect.contains lost "indeterminate" "and the model refused the step production re-invoked"
                    Expect.contains lost "invoked" "so the invoked ordinals part"
                }

                test "the faithful differential over the same journals agrees — the bend is what lost" {
                    // The control for the three cases above: without the bend,
                    // the same journals agree, so each loss is the bend's.
                    for journal in [ completedRun (); interruptedBetweenOps () ] do
                        replayDifferential DurableServices.create journal recorded |> ignore

                    let accepting =
                        DurableServices.create |> DurableServices.acceptingIndeterminateReplay

                    replayDifferential accepting (crashedInsideSecondOp accepting ()) recorded
                    |> ignore
                } ] ]

// ─── the journal store, and the kill-and-resume family (Phase 2589) ─────────
//
// Everything above crashes and replays inside ONE process, over one journal
// value — which is all an in-memory journal can show. What follows kills the
// run and resumes it through a FRESH `JournalStore.file` over the same
// directory, so the only thing the two processes share is what reached the
// disk. The conformance half reads the corpus's `kill-and-resume-toy` family
// (`PROGRAM_WIRE.md` §10.9) and runs each scenario exactly that way.

/// A directory of its own for one test's store, removed afterwards.
let internal withDirectory (f: string -> 'T) : 'T =
    let directory =
        System.IO.Path.Combine(System.IO.Path.GetTempPath(), "fuaran-journal-" + System.Guid.NewGuid().ToString "N")

    try
        f directory
    finally
        if System.IO.Directory.Exists directory then
            System.IO.Directory.Delete(directory, true)

/// The process killed after `performances` results are recorded, at the next
/// attempt — between two steps, the record of the earlier one on disk.
let private killedAfter (performances: int) (inner: EffectJournal) : EffectJournal =
    let mutable recorded = 0

    { inner with
        Append =
            fun entry ->
                match entry.Phase with
                | JournalPhase.Attempted when entry.Step >= 0 && recorded >= performances ->
                    raise (ProcessDied "killed")
                | JournalPhase.Completed _
                | JournalPhase.Refused _ when entry.Step >= 0 ->
                    inner.Append entry
                    recorded <- recorded + 1
                | _ -> inner.Append entry }

let private entry step capability subject phase =
    { Invocation = "run"
      Step = step
      Capability = capability
      Subject = subject
      Phase = phase }

let private storeUnits =
    testList
        "the journal store"
        [ test "an entry's stored form round-trips every phase, with and without a subject" {
              for e in
                  [ entry 0 "host:audit" None JournalPhase.Attempted
                    entry 0 "host:audit" None (JournalPhase.Completed(JObj [ "rows", JArr [ JInt 1; JStr "two" ] ]))
                    entry 1 Durable.OpStageCapability (Some "sha256:ab") (JournalPhase.Refused "declined")
                    entry Journal.InvocationStep Journal.InvocationCapability None (JournalPhase.Completed(JStr "")) ] do
                  let text = Journal.render e
                  Expect.isFalse (text.Contains "\n") "one line"

                  Expect.equal (Json.parse text |> Result.bind (Journal.decode >> Result.mapError _.Detail)) (Ok e) text
          }

          test "a stored form with an undeclared member or an unknown phase is refused" {
              let refused (text: string) =
                  match Json.parse text |> Result.map Journal.decode with
                  | Ok(Error _) -> true
                  | _ -> false

              Expect.isTrue
                  (refused """{"$type":"Attempted","capability":"c","extra":1,"invocation":"run","step":0}""")
                  "an undeclared member"

              Expect.isTrue (refused """{"$type":"Lost","capability":"c","invocation":"run","step":0}""") "a phase"
              Expect.isTrue (refused """{"$type":"Completed","capability":"c","invocation":"run","step":0}""") "a value"
          }

          test "the file store keeps each run's entries, in order, across a fresh instance" {
              withDirectory (fun directory ->
                  let first = JournalStore.file directory
                  Expect.isTrue first.Journal.SurvivesRestart "the file store claims to survive a restart"
                  Expect.isEmpty (first.Journal.Read "run") "opening a run with no record reads nothing"
                  let a = entry 0 "host:audit" None JournalPhase.Attempted
                  let b = entry 0 "host:audit" None (JournalPhase.Completed(JStr "ok"))
                  first.Journal.Append a
                  first.Journal.Append { a with Invocation = "other run" }
                  first.Journal.Append b

                  let restarted = JournalStore.file directory
                  Expect.equal (restarted.Journal.Read "run") [ a; b ] "the record outlived the instance"
                  Expect.equal (restarted.Journal.Read "other run") [ { a with Invocation = "other run" } ] "per run")
          }

          test "an append a kill interrupted is ignored, and cut off by the next append" {
              withDirectory (fun directory ->
                  let store = JournalStore.file directory
                  let a = entry 0 "host:audit" None JournalPhase.Attempted
                  store.Journal.Append a
                  let path = JournalStore.fileOf directory "run"
                  System.IO.File.AppendAllText(path, """{"$type":"Comp""")
                  Expect.equal (store.Journal.Read "run") [ a ] "the torn tail was never acknowledged"
                  let b = entry 0 "host:audit" None (JournalPhase.Completed(JStr "ok"))
                  store.Journal.Append b
                  Expect.equal ((JournalStore.file directory).Journal.Read "run") [ a; b ] "the tail was cut, not kept"
                  Expect.isTrue (System.IO.File.ReadAllText(path).EndsWith "\n") "every line is whole")
          }

          test "a damaged line inside the record is refused loudly, never read past" {
              withDirectory (fun directory ->
                  let store = JournalStore.file directory
                  store.Journal.Append(entry 0 "host:audit" None JournalPhase.Attempted)
                  System.IO.File.AppendAllText(JournalStore.fileOf directory "run", "not a record\n")

                  Expect.throwsT<System.IO.InvalidDataException>
                      (fun () -> store.Journal.Read "run" |> ignore)
                      "a read past a lost record would re-run the effect it recorded")
          }

          test "a run closes only once it has completed, and its file goes with it" {
              withDirectory (fun directory ->
                  let store = JournalStore.file directory
                  Expect.equal (store.Close "run") (Ok()) "nothing recorded: nothing to retire"
                  store.Journal.Append(entry 0 "host:audit" None JournalPhase.Attempted)
                  Expect.equal (store.Close "run") (Error JournalStore.RunIncomplete) "an incomplete run is a resume's"
                  Expect.isTrue (System.IO.File.Exists(JournalStore.fileOf directory "run")) "and is kept"

                  store.Journal.Append(
                      entry Journal.InvocationStep Journal.InvocationCapability None (JournalPhase.Completed(JStr "x"))
                  )

                  Expect.equal (store.Close "run") (Ok()) "a completed run closes"
                  Expect.isFalse (System.IO.File.Exists(JournalStore.fileOf directory "run")) "its file is deleted"
                  Expect.equal (store.Close "run") (Ok()) "a second close answers as the first")
          }

          test "the in-memory store closes on the same terms and claims no restart" {
              let store = JournalStore.inMemory ()
              Expect.isFalse store.Journal.SurvivesRestart "in memory dies with the process"
              store.Journal.Append(entry 0 "host:audit" None JournalPhase.Attempted)

              store.Journal.Append
                  { (entry 0 "host:audit" None JournalPhase.Attempted) with
                      Invocation = "kept" }

              Expect.equal (store.Close "run") (Error JournalStore.RunIncomplete) "incomplete"

              store.Journal.Append(
                  entry Journal.InvocationStep Journal.InvocationCapability None (JournalPhase.Completed(JStr "x"))
              )

              Expect.equal (store.Close "run") (Ok()) "complete"
              Expect.isEmpty (store.Journal.Read "run") "retired"
              Expect.isNonEmpty (store.Journal.Read "kept") "another run untouched"
          }

          test "a run under the file store derives the restart-surviving discipline" {
              withDirectory (fun directory ->
                  let services =
                      DurableServices.create
                      |> DurableServices.withStore (JournalStore.file directory)

                  Expect.equal
                      (Durable.discipline services)
                      (PlacementDiscipline.DeterministicReplay
                          { JournalSurvivesRestart = true
                            ReinvokeIndeterminate = false })
                      "the store's claim reaches the facets")
          }

          test "killed between two op stages, a fresh store resumes the run and performs each op once" {
              withDirectory (fun directory ->
                  let log = OpLog()
                  let audit = Counter()

                  let died =
                      crashing (fun () ->
                          runEdits
                              (DurableServices.create
                               |> DurableServices.withJournal (killedAfter 1 (JournalStore.file directory).Journal))
                              (auditRegistry audit)
                              (performing log)
                              editsThenAudit)

                  Expect.isTrue died "the run was killed"
                  Expect.equal log.Performed [ enc relabelTitle ] "the first op performed before the kill"
                  let store = JournalStore.file directory
                  Expect.equal (store.Close "inv") (Error JournalStore.RunIncomplete) "the dead run is kept"

                  let resumed =
                      runEdits
                          (DurableServices.create |> DurableServices.withStore store)
                          (auditRegistry audit)
                          (performing log)
                          editsThenAudit

                  Expect.isTrue resumed.Outcome.Committed "the resume committed"
                  Expect.equal resumed.Replayed [ 0 ] "the recorded op stage was served"
                  Expect.equal log.Performed [ enc relabelTitle; enc relabelFooter ] "each op performed once"
                  Expect.equal audit.Count 1 "the host call performed once"
                  Expect.equal (store.Close "inv") (Ok()) "the completed run closes")
          } ]

/// The corpus's kill-and-resume family (§10.9), read and run at the toy witness.
module KillAndResume =

    [<Literal>]
    let Family = "kill-and-resume-toy"

    [<Literal>]
    let Obligation = "durable-journal"

    /// §10.9's one performer set: three host functions, each answering, each
    /// counted.
    [<Literal>]
    let ToyCounting = "toy-counting"

    type Scenario =
        { Name: string
          Run: Handler<ToyAction, ToyOp>
          Resume: Handler<ToyAction, ToyOp>
          KillAfter: int
          BeforeKill: string list
          Committed: bool
          Performed: string list
          Served: int
          Refusal: string option }

    let private memberOf (path: string list) (value: JVal) : JVal option =
        path
        |> List.fold (fun v name -> v |> Option.bind (Fuaran.Program.Bounded.ProgramWire.tryMember name)) (Some value)

    let private fns (value: JVal option) : string list option =
        match value with
        | Some(JArr items) ->
            items
            |> List.map (function
                | JStr s -> Some s
                | _ -> None)
            |> List.fold (fun acc x -> Option.map2 (fun l y -> l @ [ y ]) acc x) (Some [])
        | _ -> None

    /// The family's scenarios, enumerated from the MANIFEST, never the
    /// directory, each read from its three files.
    let load (root: string) : Result<Scenario list, string> =
        let read (file: string) =
            System.IO.File.ReadAllText(System.IO.Path.Combine(root, file))

        let scenario (s: JVal) : Result<Scenario, string> =
            let text (path: string list) =
                match memberOf path s with
                | Some(JStr v) -> Ok v
                | _ -> Error(sprintf "no string at %s" (String.concat "." path))

            let handler (file: string) =
                HandlerWire.decodeHandler witness (read file) |> Result.mapError _.Detail

            match
                text [ "name" ],
                text [ "requires" ],
                text [ "hostPerformers" ],
                text [ "files"; "run" ] |> Result.bind handler,
                text [ "files"; "resume" ] |> Result.bind handler,
                text [ "files"; "expectation" ] |> Result.bind (read >> Json.parse)
            with
            | Ok name, Ok Obligation, Ok ToyCounting, Ok run, Ok resume, Ok e ->
                match
                    memberOf [ "kill"; "afterPerformances" ] e,
                    fns (memberOf [ "beforeKill"; "performed" ] e),
                    memberOf [ "resume"; "committed" ] e,
                    fns (memberOf [ "resume"; "performed" ] e),
                    memberOf [ "resume"; "served" ] e
                with
                | Some(JInt after), Some before, Some(JBool committed), Some performed, Some(JInt served) ->
                    Ok
                        { Name = name
                          Run = run
                          Resume = resume
                          KillAfter = after
                          BeforeKill = before
                          Committed = committed
                          Performed = performed
                          Served = served
                          Refusal =
                            match memberOf [ "resume"; "refusal" ] e with
                            | Some(JStr r) -> Some r
                            | _ -> None }
                | _ -> Error(name + ": the expectation is not §10.9's shape")
            | Ok name, Ok _, Ok _, Ok _, Ok _, Ok _ -> Error(name + ": not a scenario this host can construct")
            | name, requires, performers, run, resume, e ->
                let why =
                    function
                    | Error why -> Some why
                    | Ok _ -> None

                [ why name; why requires; why performers; why run; why resume; why e ]
                |> List.choose id
                |> List.head
                |> Error

        match Json.parse (read "manifest.json") with
        | Error e -> Error("the manifest does not parse: " + e)
        | Ok manifest ->
            match memberOf [ "durableScenarios" ] manifest with
            | Some(JArr all) ->
                all
                |> List.filter (fun s -> memberOf [ "family" ] s = Some(JStr Family))
                |> List.fold
                    (fun acc s ->
                        acc
                        |> Result.bind (fun made -> scenario s |> Result.map (fun x -> made @ [ x ])))
                    (Ok [])
            | _ -> Error "the manifest declares no durableScenarios array"

    /// What one process saw: the functions it performed, in order, and the run.
    type private Seen =
        { Performed: string list
          Outcome: DurableOutcome<ToyNode, ToyStore, ToyOp, ToyEffect> option }

    /// Run `handler` as one process over `journal`; a kill is observed, not
    /// thrown.
    let private processRun (journal: EffectJournal) (handler: Handler<ToyAction, ToyOp>) : Seen =
        let performed = ResizeArray<string>()

        let registry =
            [ "first"; "second"; "other" ]
            |> List.fold
                (fun r fn ->
                    ServerEffectRegistry.register
                        fn
                        (fun _ ->
                            performed.Add fn
                            Ok(JStr "done"))
                        r)
                ServerEffectRegistry.denyAll
            |> ServerEffectRegistry.permissive

        let outcome =
            try
                Some(
                    Durable.run
                        witness
                        (DurableServices.create |> DurableServices.withJournal journal)
                        "kill-and-resume"
                        registry
                        Fuaran.Compute.DataFrame.noResolve
                        "node"
                        handler
                        emptyStore
                )
            with ProcessDied _ ->
                None

        { Performed = List.ofSeq performed
          Outcome = outcome }

    /// The scenario, as §10.9 runs it: the run killed, a FRESH store over the
    /// same directory (`restart`), the resume, the completed run closed.
    /// Answers the first divergence from the expectation, or `None`.
    let check (restart: string -> JournalStore) (scenario: Scenario) : string option =
        withDirectory (fun directory ->
            let first =
                processRun (killedAfter scenario.KillAfter (JournalStore.file directory).Journal) scenario.Run

            let store = restart directory
            let second = processRun store.Journal scenario.Resume

            let refusal (o: DurableOutcome<_, _, _, _>) =
                o.Outcome.Diagnostics
                |> List.tryPick (function
                    | ServerDiagnostic.PerformFailed(_, reason) -> Some reason
                    | _ -> None)

            let differs what (seen: 'T) (expected: 'T) =
                if seen = expected then
                    None
                else
                    Some(sprintf "%s: %A, expected %A" what seen expected)

            match first.Outcome, second.Outcome with
            | Some _, _ -> Some "the run was not killed"
            | None, None -> Some "the resume was killed"
            | None, Some o ->
                [ fun () -> differs "performed before the kill" first.Performed scenario.BeforeKill
                  fun () -> differs "the resume committed" o.Outcome.Committed scenario.Committed
                  fun () -> differs "performed on resume" second.Performed scenario.Performed
                  fun () -> differs "served on resume" (List.length o.Replayed) scenario.Served
                  fun () -> differs "the resume's refusal" (refusal o) scenario.Refusal
                  fun () -> differs "closing the completed run" (store.Close "kill-and-resume") (Ok())
                  fun () ->
                      differs
                          "the closed run's file is present"
                          (System.IO.File.Exists(JournalStore.fileOf directory "kill-and-resume"))
                          false ]
                |> List.tryPick (fun c -> c ()))

/// The family's tests: present, every scenario as §10.9 runs it, and a GO RED
/// case that hands the resume a store which kept nothing.
let private family =
    let scenarios =
        match KillAndResume.load ToyCorpus.fixturesRoot with
        | Ok scenarios -> scenarios
        | Error e -> failwith e

    let present =
        test "the family is present and enumerated" {
            Expect.isNonEmpty scenarios "the corpus enumerates no kill-and-resume-toy scenario"
            Expect.isTrue (scenarios |> List.exists (fun s -> s.Committed)) "a scenario resumes and completes"
            Expect.isTrue (scenarios |> List.exists (fun s -> s.Refusal.IsSome)) "a scenario is refused"
        }

    let each =
        scenarios
        |> List.map (fun scenario ->
            test scenario.Name {
                match KillAndResume.check JournalStore.file scenario with
                | Some divergence -> failtestf "%s: %s" scenario.Name divergence
                | None -> ()
            })

    let goRed =
        test "GO RED: a resume over a store that did not survive the kill performs the effect again" {
            // The same scenario, its resume handed a store that kept nothing —
            // an in-memory one, as a restart leaves it. The first call is
            // performed a second time and nothing is served, and the check
            // must say so.
            let scenario = scenarios |> List.find (fun s -> s.Committed)

            Expect.isSome
                (KillAndResume.check (fun _ -> JournalStore.inMemory ()) scenario)
                "a resume without the record is told apart from one with it"
        }

    testList "the kill-and-resume-toy family (PROGRAM_WIRE.md §10.9)" ([ present ] @ each @ [ goRed ])

[<Tests>]
let storeTests =
    testList "Phase 2589 - a restart-surviving journal store, and the kill-and-resume family" [ storeUnits; family ]
