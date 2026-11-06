/// Witness coverage (fuaran#2590; the program wire's section 10.10): which witness families exercise each
/// contract member, DERIVED from the conformance corpus's manifest, and the block of `STABILITY.md` that
/// records it.
///
/// One source, two callers. `witness-coverage.fsx` beside this file `#load`s it to check or rewrite the
/// record; the test project compiles it in, so the suite pins the derivation on fabricated manifests and
/// fails the gate when the committed record has drifted from the real one. It reads the manifest through
/// `System.Text.Json` alone, so the script needs no build.
module Fuaran.Program.Tools.WitnessCoverage

open System
open System.Text.Json

/// The three classes of contract member the specification names (section 10.10).
type MemberClass =
    /// A document kind: exercised by every vector whose `document` it is.
    | Document
    /// A name a scenario's `requires` spells: exercised by every scenario and durable scenario requiring it.
    | Obligation
    /// A profile (section 10.8): exercised by every profile vector naming it.
    | Profile

/// One member and the witness families that exercise it, distinct and in ordinal order.
type Coverage =
    { Member: string
      Class: MemberClass
      Families: string list }

let classToken (memberClass: MemberClass) : string =
    match memberClass with
    | Document -> "document"
    | Obligation -> "obligation"
    | Profile -> "profile"

/// Section 10.10's rule: a member with fewer than two witness families is PROPOSED.
let isProposed (coverage: Coverage) : bool = coverage.Families.Length < 2

/// The manifest's entries in one array, each read as (the member it exercises, the families it names).
/// An entry naming no `witnesses`, or no member, RAISES: a member whose coverage cannot be computed must
/// not read as one with less of it.
let private entries (root: JsonElement) (array: string) (memberName: string) : (string * string list) list =
    match root.TryGetProperty array with
    | false, _ -> []
    | true, items ->
        [ for item in items.EnumerateArray() ->
              let id =
                  match item.TryGetProperty "id" with
                  | true, value -> value.GetString()
                  | false, _ -> "(anonymous entry)"

              let exercised =
                  match item.TryGetProperty memberName with
                  | true, value when value.ValueKind = JsonValueKind.String -> value.GetString()
                  | _ -> failwithf "manifest %s entry %s names no %s" array id memberName

              let families =
                  match item.TryGetProperty "witnesses" with
                  | true, value when value.ValueKind = JsonValueKind.Array && value.GetArrayLength() > 0 ->
                      [ for family in value.EnumerateArray() -> family.GetString() ]
                  | _ -> failwithf "manifest %s entry %s names no witnesses (section 10.10)" array id

              exercised, families ]

/// Every member the manifest's entries exercise, with its witness families: documents, then obligations,
/// then profiles, each in ordinal order of the member's name.
let derive (manifestJson: string) : Coverage list =
    use document = JsonDocument.Parse manifestJson
    let root = document.RootElement

    let ofClass memberClass sources =
        sources
        |> List.concat
        |> List.groupBy fst
        |> List.map (fun (name, exercising) ->
            { Member = name
              Class = memberClass
              Families =
                exercising
                |> List.collect snd
                |> List.distinct
                |> List.sortWith (fun a b -> String.CompareOrdinal(a, b)) })
        |> List.sortWith (fun a b -> String.CompareOrdinal(a.Member, b.Member))

    ofClass Document [ entries root "vectors" "document" ]
    @ ofClass
        Obligation
        [ entries root "scenarios" "requires"
          entries root "durableScenarios" "requires" ]
    @ ofClass Profile [ entries root "profileVectors" "profile" ]

let beginMarker =
    "<!-- witness-coverage: derived from the specification manifest by tools/witness-coverage.fsx; do not edit by hand -->"

let endMarker = "<!-- /witness-coverage -->"

/// The record, markers included, as `STABILITY.md` carries it.
let render (coverage: Coverage list) : string =
    let row (c: Coverage) =
        let mark = if isProposed c then ", **PROPOSED**" else ""
        let families = c.Families |> List.map (sprintf "`%s`") |> String.concat ", "
        $"| `{c.Member}` | {classToken c.Class}{mark} | {c.Families.Length} | {families} |"

    [ yield beginMarker
      yield "| Member | Class | Witnesses | Families |"
      yield "|---|---|---|---|"
      yield! coverage |> List.map row
      yield endMarker ]
    |> String.concat "\n"

/// The block a document carries between the markers, markers included; `None` when it carries none.
let recorded (stability: string) : string option =
    let start = stability.IndexOf(beginMarker, StringComparison.Ordinal)
    let finish = stability.IndexOf(endMarker, StringComparison.Ordinal)

    if start < 0 || finish < start then
        None
    else
        Some(stability.Substring(start, finish + endMarker.Length - start).Replace("\r\n", "\n"))

/// The document with its block replaced by `block`. Refuses a document carrying no block: where the
/// record sits is an authoring decision, and a script that invented a place would make it.
let splice (stability: string) (block: string) : Result<string, string> =
    let start = stability.IndexOf(beginMarker, StringComparison.Ordinal)
    let finish = stability.IndexOf(endMarker, StringComparison.Ordinal)

    if start < 0 || finish < start then
        Error "the document carries no witness-coverage block to rewrite"
    else
        Ok(
            stability.Substring(0, start)
            + block
            + stability.Substring(finish + endMarker.Length)
        )
