/// fuaran#2461 — what a typed read costs, and what the journalled clock read
/// costs, each as a median of N.
///
/// Two measurements, both over this repository's own surface:
///
///   * ONE LARGE TYPED READ (`Reads.Read`, Phase 2175, D41): a store document of
///     records read once through a codec, beside the codec's decode alone and
///     a SHA-256 over the same content alone, so the read's overhead over its
///     decode can be read off the figures. Then the second read of the same
///     subject, unchanged and moved, which is the only read the memo serves.
///   * THE CLOCK READ (Phase 2260, D52): a durable invocation of one host call
///     over the toy witness, unlimited and under a per-window limit. The
///     difference is the clock read and one windowed decision, journaled; the
///     journal's append count says how many records each costs a host.
///
/// Every timed read is also CHECKED — its answer and the decodes it ran — so a
/// run that measured a read which did nothing fails rather than reporting a
/// fast figure. No timing is asserted: a figure is evidence, not a gate.
///
/// `dotnet run -c Release --project tests/Fuaran.Program.Bench -- --measure`
/// is the measured run (a 21 MB store, N = 9); with no argument — the gate's
/// run — it is the quick one (1 MB, N = 5).
module Fuaran.Program.Bench.Program

open System.Diagnostics
open Fuaran.Core
open Fuaran.Program.Bounded
open Fuaran.Program.Server
open Fuaran.Program.Tests.ToyDomain

type private Settings =
    { Bytes: int
      Repeats: int
      ClockRuns: int }

let private quick =
    { Bytes = 1_000_000
      Repeats = 5
      ClockRuns = 200 }

let private measured =
    { Bytes = 21_000_000
      Repeats = 9
      ClockRuns = 2_000 }

let mutable private failures = 0

let private check (ok: bool) (what: string) =
    if not ok then
        failures <- failures + 1
        eprintfn "CHECK FAILED: %s" what

/// The median of `repeats` timings of `run`, in milliseconds, after one
/// untimed warm-up. `setup` runs before each timing, outside it.
let private medianMs (repeats: int) (setup: unit -> 'S) (run: 'S -> unit) : float =
    run (setup ())

    let timings =
        [ for _ in 1..repeats do
              let state = setup ()
              let watch = Stopwatch.StartNew()
              run state
              watch.Stop()
              watch.Elapsed.TotalMilliseconds ]
        |> List.sort

    timings[timings.Length / 2]

/// A store document of about `bytes` characters: an array of records.
let private document (bytes: int) (salt: int) : string =
    let text = System.Text.StringBuilder(bytes + 128)
    text.Append('[') |> ignore
    let mutable i = 0

    while text.Length < bytes do
        if i > 0 then
            text.Append(',') |> ignore

        text.Append($"{{\"node\":\"n-{i}\",\"note\":null,\"weight\":{(i + salt) % 10}}}")
        |> ignore

        i <- i + 1

    text.Append(']').ToString()

/// The store's codec: the record count, read null-tolerantly.
let private codec: ReadCodec<int> =
    { Name = "bench-records-v1"
      Decode =
        fun text ->
            match Decoder.parse ReadOptions.tolerantOfNull text with
            | Ok(JArr items) -> Ok(List.length items)
            | Ok _ -> Error "a store document is an array"
            | Error error -> Error(DecodeError.describe error) }

let private reportMs (what: string) (repeats: int) (ms: float) =
    printfn "  %-58s median %10.2f ms  (N = %d)" what ms repeats

let private typedRead (settings: Settings) =
    let content = document settings.Bytes 0
    // The same length, one digit moved: the rewrite a metadata key would miss.
    let moved = document settings.Bytes 1
    check (moved.Length = content.Length && moved <> content) "the moved document is a same-length rewrite"

    let expected =
        match codec.Decode content with
        | Ok count -> count
        | Error reason -> failwithf "the bench document does not decode: %s" reason

    printfn
        "one large typed read — a store document of %.1f MB, %d records"
        (float content.Length / 1_000_000.0)
        expected

    let read (reads: Reads) (text: string) =
        reads.Read(codec, "store", (fun () -> Ok text))

    let decodeMs =
        medianMs settings.Repeats ignore (fun () -> check (codec.Decode content = Ok expected) "the decode answers")

    let hashMs =
        medianMs settings.Repeats ignore (fun () -> Hash.sha256Hex content |> ignore)

    let singleMs =
        medianMs settings.Repeats (fun () -> Reads.Over EntryReader.live) (fun reads ->
            check (read reads content = Ok(Read.Available expected)) "a single read answers the decode"
            check (reads.Decodes = 1) "a single read decodes once")

    let primed () =
        let reads = Reads.Over EntryReader.live
        read reads content |> ignore
        reads

    // A re-read of a store answers a NEW string with the same characters, never
    // the instance the first read held: the copy is made outside the timing.
    let repeatMs =
        medianMs settings.Repeats (fun () -> primed (), System.String(content.ToCharArray())) (fun (reads, reread) ->
            check (read reads reread = Ok(Read.Available expected)) "a repeat read answers the memo"
            check (reads.Decodes = 1) "a repeat read of unchanged content decodes nothing")

    let movedMs =
        medianMs settings.Repeats primed (fun reads ->
            check (read reads moved = Ok(Read.Available expected)) "a moved read answers its own decode"
            check (reads.Decodes = 2) "a moved read decodes fresh")

    reportMs "the codec's decode alone" settings.Repeats decodeMs
    reportMs "a SHA-256 over the content alone" settings.Repeats hashMs
    reportMs "Reads.Read, a single read" settings.Repeats singleMs
    reportMs "Reads.Read, a second read of unchanged content" settings.Repeats repeatMs
    reportMs "Reads.Read, a second read of moved same-length content" settings.Repeats movedMs
    printfn "  single read over its decode: %+.2f ms" (singleMs - decodeMs)

// ─── the clock read ──────────────────────────────────────────────────────────

let private Audit = "host:audit"

let private emptyStore: ServerStore<ToyNode, ToyStore> =
    { Tree =
        { Id = "root"
          Label = Const(JStr "root")
          Handlers = []
          Children = [] }
      Bindings = Map.empty }

let private audit: Handler<ToyAction, ToyOp> =
    { Name = "audit"
      Stages = [ Effect(ServerEffect.HostCall("audit", JObj [], None)) ] }

let private registryOf (clauses: ServerConstraintClause list) : ServerEffectRegistry =
    let registry =
        ServerEffectRegistry.denyAll
        |> ServerEffectRegistry.register "audit" (fun _ -> Ok(JStr "audited"))
        |> ServerEffectRegistry.permissive

    if List.isEmpty clauses then
        registry
    else
        ServerEffectRegistry.constrain Audit clauses registry

/// `runs` invocations, each over a fresh in-memory journal whose appends are
/// counted; answers the appends of the last.
let private invocations (runs: int) (clauses: ServerConstraintClause list) (clock: bool) : int =
    let registry = registryOf clauses
    let mutable appends = 0

    for i in 1..runs do
        let inner = Journal.inMemory ()
        appends <- 0

        let journal =
            { inner with
                Append =
                    fun entry ->
                        appends <- appends + 1
                        inner.Append entry }

        let services = DurableServices.create |> DurableServices.withJournal journal

        let services =
            if clock then
                services |> DurableServices.withClock (fun () -> 1_000L)
            else
                services

        let outcome =
            Durable.runWith
                witness
                services
                $"i{i}"
                registry
                OpPerformance.InMemory
                Fuaran.Compute.DataFrame.noResolve
                "root"
                audit
                emptyStore

        check outcome.Outcome.Committed "the invocation committed"

    appends

let private clockRead (settings: Settings) =
    printfn "the journalled clock read — a durable invocation of one host call, in-memory journal"
    let limit = [ ServerConstraintClause.PerWindow(1_000_000, 1_000) ]
    let perRun ms = ms * 1000.0 / float settings.ClockRuns

    let plainMs =
        medianMs settings.Repeats ignore (fun () -> invocations settings.ClockRuns [] false |> ignore)

    let limitedMs =
        medianMs settings.Repeats ignore (fun () -> invocations settings.ClockRuns limit true |> ignore)

    let plainAppends = invocations 1 [] false
    let limitedAppends = invocations 1 limit true

    printfn "  %-58s median %10.2f us  (%d appends)" "an invocation, unlimited" (perRun plainMs) plainAppends

    printfn
        "  %-58s median %10.2f us  (%d appends)"
        "an invocation under a per-window limit (clock + decision)"
        (perRun limitedMs)
        limitedAppends

    printfn
        "  the clock read and one decision: %+.2f us and %d journal appends per invocation (N = %d batches of %d)"
        (perRun (limitedMs - plainMs))
        (limitedAppends - plainAppends)
        settings.Repeats
        settings.ClockRuns

[<EntryPoint>]
let main argv =
    let settings = if Array.contains "--measure" argv then measured else quick

    printfn "Fuaran.Program bench (fuaran#2461) — %s run" (if settings = measured then "measured" else "quick")

    typedRead settings
    clockRead settings

    if failures > 0 then
        eprintfn "%d check(s) failed" failures
        1
    else
        0
