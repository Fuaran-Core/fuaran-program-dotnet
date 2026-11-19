/// The file journal store across PROCESSES (Phase 2797, D72): one live process
/// holds a run, and the store enforces it.
///
/// Every other journal test runs inside one process, which is the one place
/// this property cannot be seen: a hold is the process's, so a second store in
/// the same process shares it. These tests start CHILD PROCESSES — this test
/// runner itself, filtered by Expecto's own `--filter-test-case` to the one
/// case below that acts only when the parent's environment variables tell it
/// to — and read what each one did:
///
///   * a second live process asking for a held run is refused with
///     `JournalStore.RunHeld`, naming the run, and writes nothing;
///   * a process that dies holding a run does not block the next, which takes
///     the run and resumes from what the dead one recorded;
///   * two processes holding different runs under one directory do not block
///     each other;
///   * a runtime with file locking switched off is refused with
///     `JournalStore.HoldUnavailable` rather than trusted — on Linux and macOS,
///     where the switch exists; on Windows a share mode is the system's and the
///     switch changes nothing, so there the run is held.
///
/// Every child is ended on every path, failures included.
module Fuaran.Program.Tests.JournalStoreProcessTests

open System
open System.Diagnostics
open System.IO
open Expecto
open Fuaran.Program.Server

/// The child's case name: matched by `--filter-test-case`, and by nothing the
/// parent's own cases are called.
[<Literal>]
let private ChildCase = "journal-store-child-process"

/// What the child does: `hold` or `try`. Unset in every ordinary run, where
/// the child case is not registered at all.
[<Literal>]
let private ModeVariable = "FUARAN_JOURNAL_CHILD_MODE"

[<Literal>]
let private DirectoryVariable = "FUARAN_JOURNAL_CHILD_DIRECTORY"

[<Literal>]
let private RunVariable = "FUARAN_JOURNAL_CHILD_RUN"

/// Where the child writes what happened, once, whole.
[<Literal>]
let private ReportVariable = "FUARAN_JOURNAL_CHILD_REPORT"

/// The capability the child's one record is filed under, so the parent can
/// tell the child's record from anything else in the file.
[<Literal>]
let private ChildCapability = "HostCall:child"

/// The longest a holding child lives if nobody ends it: a bound on an orphan,
/// never a timing the tests rely on.
let private orphanBound = TimeSpan.FromMinutes 3.0

let private report (text: string) =
    let path = Environment.GetEnvironmentVariable ReportVariable
    let partial = path + ".partial"
    File.WriteAllText(partial, text)
    File.Move(partial, path, true)

/// The child's act. `hold`: read the run (taking the hold), append one
/// `Attempted` record, report `held`, and stay alive until ended. `try`: read
/// and append once, and report `ok` or the refusal's class.
let private childAct (mode: string) =
    let store = JournalStore.file (Environment.GetEnvironmentVariable DirectoryVariable)

    let run = Environment.GetEnvironmentVariable RunVariable

    let act () =
        let recorded = store.Journal.Read run

        store.Journal.Append
            { Invocation = run
              Step = List.length recorded
              Capability = ChildCapability
              Subject = None
              Phase = JournalPhase.Attempted }

    match mode with
    | "hold" ->
        act ()
        report "held"
        Threading.Thread.Sleep orphanBound
    | _ ->
        try
            act ()
            report "ok"
        with :? JournalStoreRefusedException as e ->
            report e.Refusal

/// The child case, registered only in a child.
[<Tests>]
let childProcess =
    match Environment.GetEnvironmentVariable ModeVariable with
    | null
    | "" -> testList "journal store child (inactive outside a child)" []
    | mode -> testCase ChildCase (fun () -> childAct mode)

/// One started child, and where it reports.
type private Child = { Process: Process; Report: string }

/// Start this runner as a child in `mode` on `run` under `directory`, with
/// `extra` added to its environment.
let private start (mode: string) (directory: string) (run: string) (extra: (string * string) list) : Child =
    let host = Environment.ProcessPath

    let info = ProcessStartInfo host

    // Run as `dotnet <tests>.dll` or as the apphost: whichever this runner is.
    if Path.GetFileNameWithoutExtension(host).Equals("dotnet", StringComparison.OrdinalIgnoreCase) then
        info.ArgumentList.Add(typeof<Child>.Assembly.Location)

    info.ArgumentList.Add "--filter-test-case"
    info.ArgumentList.Add ChildCase
    info.UseShellExecute <- false
    info.RedirectStandardOutput <- true
    info.RedirectStandardError <- true

    // The report's directory is the store's; created here, so a child that
    // fails before its store creates it still has somewhere to report.
    Directory.CreateDirectory directory |> ignore

    let reportPath =
        Path.Combine(directory, "child-" + Guid.NewGuid().ToString "N" + ".report")

    info.Environment.[ModeVariable] <- mode
    info.Environment.[DirectoryVariable] <- directory
    info.Environment.[RunVariable] <- run
    info.Environment.[ReportVariable] <- reportPath

    for name, value in extra do
        info.Environment.[name] <- value

    let child = Process.Start info
    // Drained, so a chatty child never blocks on a full pipe.
    child.OutputDataReceived.Add ignore
    child.ErrorDataReceived.Add ignore
    child.BeginOutputReadLine()
    child.BeginErrorReadLine()
    { Process = child; Report = reportPath }

/// The child's report, waiting for it while the child lives; `None` if it
/// ended, or the wait ran out, with nothing reported.
let private awaitReport (child: Child) : string option =
    let deadline = DateTime.UtcNow + TimeSpan.FromMinutes 2.0

    let rec poll () =
        if File.Exists child.Report then
            Some(File.ReadAllText child.Report)
        elif child.Process.HasExited || DateTime.UtcNow > deadline then
            if File.Exists child.Report then
                Some(File.ReadAllText child.Report)
            else
                None
        else
            Threading.Thread.Sleep 50
            poll ()

    poll ()

/// End a child and wait until it has gone: the operating system has then
/// released everything it held. Ending an ended child does nothing.
let private ending (child: Child) =
    if not child.Process.HasExited then
        child.Process.Kill true

    child.Process.WaitForExit()

/// `f` with every started child ended afterwards, on every path.
let private withChildren (f: (Child -> Child) -> 'T) : 'T =
    let started = Collections.Generic.List<Child>()

    try
        f (fun child ->
            started.Add child
            child)
    finally
        for child in started do
            ending child

/// A child holding `run`, once it has said so.
let private holding (track: Child -> Child) (directory: string) (run: string) : Child =
    let child = track (start "hold" directory run [])
    Expect.equal (awaitReport child) (Some "held") "the child took the run and recorded one step"
    child

/// The run's journal as the bytes on disk say, without taking a hold.
let private recordedLines (directory: string) (run: string) : string list =
    let path = JournalStore.fileOf directory run

    if File.Exists path then
        File.ReadAllLines path |> List.ofArray
    else
        []

let private refusal (f: unit -> 'T) : JournalStoreRefusedException option =
    try
        f () |> ignore
        None
    with :? JournalStoreRefusedException as e ->
        Some e

[<Tests>]
let tests =
    testList
        "the file journal store across processes (Phase 2797)"
        [ test "a second live process asking for a held run is refused, naming the run, and writes nothing" {
              ToyDurableReplayTests.withDirectory (fun directory ->
                  withChildren (fun track ->
                      let child = holding track directory "run"
                      let before = recordedLines directory "run"
                      Expect.equal (List.length before) 1 "the holder's one record"

                      let store = JournalStore.file directory

                      match refusal (fun () -> store.Journal.Read "run") with
                      | None -> failtest "a read of a run another live process holds was admitted"
                      | Some e ->
                          Expect.equal e.Refusal JournalStore.RunHeld "refused as held"
                          Expect.equal e.Run "run" "naming the run"
                          Expect.stringContains e.Message "'run'" "and the message names it too"

                      let appended =
                          refusal (fun () ->
                              store.Journal.Append
                                  { Invocation = "run"
                                    Step = 1
                                    Capability = "HostCall:parent"
                                    Subject = None
                                    Phase = JournalPhase.Attempted })

                      Expect.equal
                          (appended |> Option.map (fun e -> e.Refusal))
                          (Some JournalStore.RunHeld)
                          "an append is refused the same way"

                      Expect.equal (store.Close "run") (Error JournalStore.RunHeld) "and a close is answered so"
                      Expect.equal (recordedLines directory "run") before "the refused process wrote nothing"
                      Expect.isFalse child.Process.HasExited "while the holder still lived"))
          }

          test "a process that dies holding a run does not block the next, which resumes from what it recorded" {
              ToyDurableReplayTests.withDirectory (fun directory ->
                  withChildren (fun track ->
                      let child = holding track directory "run"
                      ending child

                      let store = JournalStore.file directory
                      let resumed = store.Journal.Read "run"

                      Expect.equal
                          (resumed |> List.map (fun e -> e.Capability, e.Step))
                          [ ChildCapability, 0 ]
                          "the next process takes the run and reads the dead one's record"

                      store.Journal.Append
                          { Invocation = "run"
                            Step = 0
                            Capability = ChildCapability
                            Subject = None
                            Phase = JournalPhase.Completed(Fuaran.Core.JStr "done") }

                      Expect.equal (List.length (store.Journal.Read "run")) 2 "and appends to it"))
          }

          test "two processes holding different runs under one directory do not block each other" {
              ToyDurableReplayTests.withDirectory (fun directory ->
                  withChildren (fun track ->
                      let first = holding track directory "first"
                      let second = holding track directory "second"
                      let store = JournalStore.file directory

                      Expect.equal (store.Journal.Read "third") [] "a third run is this process's to take"
                      Expect.isFalse first.Process.HasExited "both holders live"
                      Expect.isFalse second.Process.HasExited "both holders live"
                      Expect.equal (List.length (recordedLines directory "first")) 1 "each wrote its own run"
                      Expect.equal (List.length (recordedLines directory "second")) 1 "each wrote its own run"))
          }

          test "a runtime with file locking switched off is refused rather than trusted, where the switch exists" {
              ToyDurableReplayTests.withDirectory (fun directory ->
                  withChildren (fun track ->
                      let child =
                          track (start "try" directory "run" [ "DOTNET_SYSTEM_IO_DISABLEFILELOCKING", "1" ])

                      let expected =
                          if OperatingSystem.IsWindows() then
                              "ok"
                          else
                              JournalStore.HoldUnavailable

                      Expect.equal (awaitReport child) (Some expected) "the hold is real, or the run is refused"

                      if not (OperatingSystem.IsWindows()) then
                          Expect.equal (recordedLines directory "run") [] "and a refused run is never written"))
          } ]
