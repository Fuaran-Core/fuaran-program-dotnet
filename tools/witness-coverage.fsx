// Witness coverage (fuaran#2590; the program wire's section 10.10): check or rewrite the block of
// STABILITY.md that records which witness families exercise each contract member.
//
//   dotnet fsi tools/witness-coverage.fsx            # check: exit 1, printing the derived block, on drift
//   dotnet fsi tools/witness-coverage.fsx --write    # rewrite the block from the manifest
//
// The manifest is the corpus's, resolved as the gate resolves it: FUARAN_PROGRAM_SPEC, else the sibling
// clone beside this repository. The gate checks the same thing through the test suite, which compiles
// the derivation this script loads.

#load "WitnessCoverage.fs"

open System
open System.IO
open Fuaran.Program.Tools.WitnessCoverage

let repository = Path.GetFullPath(Path.Combine(__SOURCE_DIRECTORY__, ".."))

let spec =
    match Environment.GetEnvironmentVariable "FUARAN_PROGRAM_SPEC" with
    | null
    | "" -> Path.Combine(repository, "..", "Fuaran-UI", "fuaran-program-spec")
    | path -> path

let manifestPath = Path.Combine(spec, "wire-fixtures", "manifest.json")
let stabilityPath = Path.Combine(repository, "STABILITY.md")

if not (File.Exists manifestPath) then
    eprintfn
        "the conformance corpus is not present at '%s'; clone it beside this repository, or point FUARAN_PROGRAM_SPEC at it"
        spec

    exit 2

let derived = File.ReadAllText manifestPath |> derive |> render
let stability = File.ReadAllText stabilityPath

if fsi.CommandLineArgs |> Array.contains "--write" then
    match splice stability derived with
    | Ok rewritten ->
        File.WriteAllText(stabilityPath, rewritten)
        printfn "rewrote the witness-coverage block in %s" stabilityPath
    | Error reason ->
        eprintfn "%s: %s" stabilityPath reason
        exit 1
elif recorded stability = Some derived then
    printfn "the witness-coverage block in STABILITY.md matches the manifest"
else
    eprintfn "the witness-coverage block in STABILITY.md has drifted from the manifest; derived:\n%s" derived
    eprintfn "rewrite it with: dotnet fsi tools/witness-coverage.fsx --write"
    exit 1
