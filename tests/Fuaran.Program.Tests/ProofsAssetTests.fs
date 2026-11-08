/// The proof models' release asset, held to its committed sha256 (Phase 2383, DECISIONS.md D67).
///
/// Another repository's proof leg takes this repository's models, runtime floor and extractions as
/// ONE archive, `proofs-program-<version>.tar`, pinned by sha256, rather than as copied files.
/// `proofs/asset.json` declares the archive's contents and commits its sha; the proof kit's builder
/// (pinned in `proofs/proofs-kit.json`, verified before it is unpacked) builds it, through
/// `proofs/check.ps1 -AssetOnly`, which is also what the publish workflow runs on a `v*` tag. This
/// family makes the sha a GATE fact: a commit that moves a declared file without moving the
/// committed sha with it is red here, long before a release tag would refuse it.
///
/// The builder comes from the pinned kit asset: the check downloads it once into `proofs/obj/kit/`
/// (or takes `FUARAN_PROOFS_KIT_ASSET`, the offline path) and refuses any other bytes.
module Fuaran.Program.Tests.ProofsAssetTests

open System
open System.Diagnostics
open System.IO
open System.Security.Cryptography
open System.Text.Json
open Expecto

let private repoRoot =
    let rec up (dir: DirectoryInfo) =
        if isNull dir then
            failwith "no Fuaran.Program.slnx above this source file"
        elif File.Exists(Path.Combine(dir.FullName, "Fuaran.Program.slnx")) then
            dir.FullName
        else
            up dir.Parent

    up (DirectoryInfo __SOURCE_DIRECTORY__)

let private proofsDir = Path.Combine(repoRoot, "proofs")

let private scratch (stem: string) =
    Path.Combine(Path.GetTempPath(), stem + "-" + Guid.NewGuid().ToString "N")

/// `pwsh -File <script> <args>`, answering its exit code and its whole output.
let private pwsh (script: string) (args: string list) : int * string =
    let info = ProcessStartInfo "pwsh"

    for a in [ "-NoProfile"; "-NonInteractive"; "-File"; script ] @ args do
        info.ArgumentList.Add a

    info.RedirectStandardOutput <- true
    info.RedirectStandardError <- true
    info.UseShellExecute <- false
    use p = Process.Start info
    let stderr = p.StandardError.ReadToEndAsync()
    let stdout = p.StandardOutput.ReadToEnd()
    p.WaitForExit()
    p.ExitCode, stdout + stderr.Result

let private sha256Of (file: string) =
    use stream = File.OpenRead file
    Convert.ToHexString(SHA256.HashData stream).ToLowerInvariant()

let private committedSha () =
    use doc =
        JsonDocument.Parse(File.ReadAllText(Path.Combine(proofsDir, "asset.json")))

    doc.RootElement.GetProperty("sha256").GetString()

/// The archive `check.ps1 -AssetOnly` built into a fresh directory, and its sha256.
let private buildAsset (proofs: string) (extra: string list) : int * string * string option =
    let out = scratch "proofs-program-asset"

    try
        let exit, output =
            pwsh (Path.Combine(proofs, "check.ps1")) ([ "-AssetOnly"; "-AssetOutDir"; out ] @ extra)

        let built =
            if Directory.Exists out then
                Directory.GetFiles(out, "proofs-program-*.tar")
                |> Array.tryExactlyOne
                |> Option.map sha256Of
            else
                None

        exit, output, built
    finally
        if Directory.Exists out then
            Directory.Delete(out, true)

/// The verified kit archive a previous run cached, so a scratch tree need not download it again.
let private cachedKit () =
    use doc =
        JsonDocument.Parse(File.ReadAllText(Path.Combine(proofsDir, "proofs-kit.json")))

    let cached =
        Path.Combine(proofsDir, "obj", "kit", doc.RootElement.GetProperty("asset").GetString())

    if File.Exists cached then [ "-KitAsset"; cached ] else []

/// A copy of this repository's proof declarations and every declared file, under a scratch root
/// that carries the version file the builder reads.
let private scratchProducer () =
    let root = scratch "proofs-program-producer"
    let proofs = Path.Combine(root, "proofs")
    Directory.CreateDirectory(Path.Combine(proofs, "oracle")) |> ignore
    File.Copy(Path.Combine(repoRoot, "Directory.Build.props"), Path.Combine(root, "Directory.Build.props"))

    for name in [ "check.ps1"; "asset.json"; "proofs-kit.json"; "fstar-pin.json" ] do
        File.Copy(Path.Combine(proofsDir, name), Path.Combine(proofs, name))

    use doc =
        JsonDocument.Parse(File.ReadAllText(Path.Combine(proofsDir, "asset.json")))

    for entry in doc.RootElement.GetProperty("files").EnumerateArray() do
        let path = entry.GetProperty("path").GetString()
        File.Copy(Path.Combine(proofsDir, path), Path.Combine(proofs, path))

    root, proofs

[<Tests>]
let tests =
    testSequenced
    <| testList
        "Proofs.Asset"
        [ testCase "the release asset this tree builds is reproducible, and its sha256 is the one asset.json commits"
          <| fun _ ->
              let firstExit, firstOutput, first = buildAsset proofsDir []
              Expect.equal firstExit 0 (sprintf "check.ps1 -AssetOnly is green over this tree: %s" firstOutput)
              let secondExit, secondOutput, second = buildAsset proofsDir (cachedKit ())
              Expect.equal secondExit 0 (sprintf "and green again: %s" secondOutput)
              Expect.isSome first "the first build wrote one proofs-program archive"
              Expect.equal first second "two builds of one tree are the same bytes"

              Expect.equal
                  first
                  (Some(committedSha ()))
                  "proofs/asset.json commits this tree's asset (check.ps1 -AssetOnly -UpdateAsset, in the same commit)"

          testCase "go-red: a planted edit to one declared model moves the sha256, and the check refuses it"
          <| fun _ ->
              let root, proofs = scratchProducer ()

              try
                  let controlExit, controlOutput, _ = buildAsset proofs (cachedKit ())
                  Expect.equal controlExit 0 (sprintf "the unedited copy is green: %s" controlOutput)
                  File.AppendAllText(Path.Combine(proofs, "Budget.fst"), "\n// a planted edit\n")
                  let exit, output, built = buildAsset proofs (cachedKit ())
                  Expect.equal exit 1 (sprintf "a moved model without a moved sha exits 1: %s" output)
                  Expect.stringContains output "-Update" "the refusal names the remedy"
                  Expect.notEqual built (Some(committedSha ())) "and the archive it built is a different one"
              finally
                  Directory.Delete(root, true)

          testCase "a kit asset whose bytes are not the pin's is refused before anything is unpacked"
          <| fun _ ->
              let root, proofs = scratchProducer ()

              try
                  let impostor = Path.Combine(root, "impostor.tar")
                  File.WriteAllText(impostor, "not the pinned kit")
                  let exit, output, built = buildAsset proofs [ "-KitAsset"; impostor ]
                  Expect.equal exit 2 (sprintf "an impostor kit exits 2: %s" output)
                  Expect.stringContains output "REFUSED the kit asset" "the refusal says what it refused"
                  Expect.isNone built "and no asset was built"
                  let kitDir = Path.Combine(proofs, "obj", "kit")

                  Expect.isEmpty
                      (if Directory.Exists kitDir then
                           Directory.GetDirectories(kitDir, "run-*")
                       else
                           [||])
                      "nothing was unpacked"
              finally
                  Directory.Delete(root, true) ]
