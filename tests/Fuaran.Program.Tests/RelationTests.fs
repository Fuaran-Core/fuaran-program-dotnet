/// Recursive questions over a finite relation, answered totally (Phase 2220,
/// D47), each property behind a law or a differential against a brute-force
/// reference that follows the definition rather than the algorithm:
///
///   * **every cycle is found** — every edge that lies on a cycle (its target
///     reaches its source) has both ends in `cyclesAmong`;
///   * **a node is in a non-trivial component exactly when it reaches itself**,
///     by one edge or more — and two nodes share a component exactly when each
///     reaches the other;
///   * **the cost is linear in nodes plus edges** — the pass's counted work is
///     exactly N + E on every relation, whatever the number of paths, and the
///     dense diamond of roadmap-engine#752 (200 deep, 4 wide, 4^200 paths) is answered fast,
///     with and without a back edge;
///   * **the order is a function of the edge SET** — reordering or repeating a
///     successor list moves no answer — and the components come in reverse
///     topological order;
///   * **closure and chain ends** agree with their references, so readiness
///     over redirects is a one-line host predicate.
module Fuaran.Program.Tests.RelationTests

open Expecto
open Fuaran.Program

// ─── the references: the definitions, by brute force ─────────────────────────

let private succOf (edges: Map<'N, 'N list>) (n: 'N) =
    Map.tryFind n edges |> Option.defaultValue []

let private nodesOf (edges: Map<'N, 'N list>) : Set<'N> =
    edges
    |> Map.fold (fun acc k vs -> Set.union (Set.add k acc) (Set.ofList vs)) Set.empty

/// Every node reachable from `n` by ONE edge or more.
let private reachPlus (edges: Map<'N, 'N list>) (n: 'N) : Set<'N> =
    let rec go (seen: Set<'N>) (todo: 'N list) =
        match todo with
        | [] -> seen
        | x :: rest ->
            let fresh =
                succOf edges x |> List.distinct |> List.filter (fun y -> not (seen.Contains y))

            go (Set.union seen (Set.ofList fresh)) (fresh @ rest)

    let first = succOf edges n |> List.distinct
    go (Set.ofList first) first

let private reachesSelf edges n = (reachPlus edges n).Contains n

/// Reachable by ZERO edges or more.
let private reachStar edges n = Set.add n (reachPlus edges n)

let private refCycles (edges: Map<'N, 'N list>) : Set<'N> =
    nodesOf edges |> Set.filter (reachesSelf edges)

let private refTerminals (edges: Map<'N, 'N list>) (n: 'N) : Set<'N> option =
    let reached = reachStar edges n

    if reached |> Set.exists (reachesSelf edges) then
        None
    else
        Some(reached |> Set.filter (fun m -> List.isEmpty (succOf edges m)))

/// A seeded random relation over ints: `size` keyed nodes, some successors
/// outside the keys, repeated successors, self-edges — every shape the
/// definitions distinguish.
let private randomRelation (seed: int) : Map<int, int list> =
    let rng = System.Random seed
    let size = 1 + rng.Next 14
    let density = rng.NextDouble() * 0.35

    [ for k in 0 .. size - 1 ->
          k,
          [ for t in 0 .. size + 2 do
                if rng.NextDouble() < density then
                    yield t

                    if rng.NextDouble() < 0.1 then
                        yield t ] ]
    |> Map.ofList

let private seeds = [ 1..400 ]

/// The dense diamond of roadmap-engine#752: every node depends on every
/// node of the layer above, so the relation has width^2 x (layers - 1) edges
/// and width ^ layers paths. `backEdge` closes a cycle L0W0 -> L(last)W0.
let private diamond (layers: int) (width: int) (backEdge: bool) : Map<string, string list> =
    [ for l in 0 .. layers - 1 do
          for w in 0 .. width - 1 ->
              sprintf "L%dW%d" l w,
              [ if l > 0 then
                    for v in 0 .. width - 1 -> sprintf "L%dW%d" (l - 1) v
                if backEdge && l = 0 && w = 0 then
                    yield sprintf "L%dW0" (layers - 1) ] ]
    |> Map.ofList

// ─── the laws ────────────────────────────────────────────────────────────────

let private cycles =
    testList
        "cycle membership"
        [ test "every cycle is found: each edge on a cycle has both ends in cyclesAmong" {
              for seed in seeds do
                  let r = randomRelation seed
                  let found = Relation.cyclesAmong r

                  for KeyValue(u, vs) in r do
                      for v in vs do
                          if (reachStar r v).Contains u then
                              Expect.isTrue
                                  (found.Contains u && found.Contains v)
                                  (sprintf "seed %d: the edge %d -> %d lies on a cycle" seed u v)
          }

          test "a node is on a cycle exactly when it reaches itself (differential against the definition)" {
              for seed in seeds do
                  let r = randomRelation seed
                  Expect.equal (Relation.cyclesAmong r) (refCycles r) (sprintf "seed %d" seed)
          }

          test "two nodes share a component exactly when each reaches the other; the components partition the nodes" {
              for seed in seeds do
                  let r = randomRelation seed
                  let components = Relation.components r

                  Expect.equal
                      (components |> List.concat |> List.sort)
                      (nodesOf r |> Set.toList)
                      (sprintf "seed %d: every node once" seed)

                  let componentOf =
                      components
                      |> List.indexed
                      |> List.collect (fun (i, members) -> members |> List.map (fun m -> m, i))
                      |> Map.ofList

                  for a in nodesOf r do
                      for b in nodesOf r do
                          let mutual = (reachStar r a).Contains b && (reachStar r b).Contains a

                          Expect.equal (componentOf[a] = componentOf[b]) mutual (sprintf "seed %d: %d and %d" seed a b)
          }

          test "cycles are exactly the components that are non-trivial, in the components' order" {
              for seed in seeds do
                  let r = randomRelation seed

                  let expected =
                      Relation.components r
                      |> List.filter (fun members ->
                          match members with
                          | [ only ] -> reachesSelf r only
                          | _ -> true)

                  Expect.equal (Relation.cycles r) expected (sprintf "seed %d" seed)
          }

          test "a self-edge is a cycle of one; a node that is only a target is a node" {
              let r = Map.ofList [ "a", [ "a"; "b" ]; "b", [ "c" ] ]
              Expect.equal (Relation.cyclesAmong r) (Set.ofList [ "a" ]) "the self-loop, nothing else"
              Expect.equal (Relation.components r) [ [ "c" ]; [ "b" ]; [ "a" ] ] "c is a node; dependencies first"
          } ]

let private order =
    testList
        "the order is canonical"
        [ test "reordering and repeating successor lists moves no answer" {
              for seed in seeds do
                  let r = randomRelation seed
                  let rng = System.Random(seed * 7919)

                  let shuffled =
                      r
                      |> Map.map (fun _ vs ->
                          let doubled = vs @ (vs |> List.filter (fun _ -> rng.Next 2 = 0))
                          doubled |> List.sortBy (fun _ -> rng.Next()))

                  let terminalsOf rel =
                      let t = Relation.terminals rel
                      nodesOf r |> Set.toList |> List.map t

                  Expect.equal (Relation.components shuffled) (Relation.components r) (sprintf "seed %d" seed)
                  Expect.equal (Relation.cycles shuffled) (Relation.cycles r) (sprintf "seed %d" seed)
                  Expect.equal (terminalsOf shuffled) (terminalsOf r) (sprintf "seed %d" seed)
          }

          test "components come in reverse topological order: each after every component it reaches" {
              for seed in seeds do
                  let r = randomRelation seed
                  let components = Relation.components r

                  let position =
                      components
                      |> List.indexed
                      |> List.collect (fun (i, members) -> members |> List.map (fun m -> m, i))
                      |> Map.ofList

                  for KeyValue(u, vs) in r do
                      for v in vs do
                          Expect.isTrue
                              (position[v] <= position[u])
                              (sprintf "seed %d: %d -> %d, the target's component first" seed u v)
          }

          test "members of a component are ascending" {
              for seed in seeds do
                  for members in Relation.components (randomRelation seed) do
                      Expect.equal members (List.sort members) (sprintf "seed %d" seed)
          } ]

let private linear =
    testList
        "the cost is linear in nodes plus edges"
        [ test "the pass's counted work is exactly N + E on every relation" {
              for seed in seeds do
                  let r = randomRelation seed
                  let n = (nodesOf r).Count

                  let e =
                      r |> Map.toList |> List.sumBy (fun (_, vs) -> List.distinct vs |> List.length)

                  Expect.equal
                      (Relation.work r)
                      (n + e)
                      (sprintf "seed %d: one finish per node, one look per edge" seed)
          }

          test "the dense diamond 200 deep - 4^200 paths - is answered in linear work, with and without a cycle" {
              let clock = System.Diagnostics.Stopwatch.StartNew()
              let acyclic = diamond 200 4 false
              let cyclic = diamond 200 4 true

              Expect.equal (Relation.work acyclic) (800 + 199 * 16) "N + E, not paths"
              Expect.isEmpty (Relation.cyclesAmong acyclic) "no cycle"

              // The back edge L0W0 -> L199W0 closes a cycle: L0W0, L199W0 and every node of layers 1..198 lie on
              // it; L199W1..L199W3 are not reachable from L0W0 and L0W1..L0W3 reach nothing.
              let onCycle = Relation.cyclesAmong cyclic
              Expect.equal onCycle.Count (2 + 198 * 4) "every node on the back edge's cycle, and no other"
              Expect.isFalse (onCycle.Contains "L0W1") "a node that reaches nothing is on no cycle"
              Expect.equal (Relation.work cyclic) (800 + 199 * 16 + 1) "N + E"

              let ends = Relation.terminals acyclic

              Expect.equal
                  (ends "L199W2")
                  (Some(Set.ofList [ "L0W0"; "L0W1"; "L0W2"; "L0W3" ]))
                  "every chain ends at layer 0"

              Expect.equal (Relation.terminals cyclic "L199W1") None "a chain into the cycle ends nowhere"

              Expect.equal
                  ((Relation.reachable acyclic [ "L199W0" ]).Count)
                  797
                  "the closure: itself and the 199 layers below"

              Expect.isLessThan clock.Elapsed.TotalSeconds 5.0 "a path enumeration would not finish"
          }

          test "a chain 200,000 long is answered without exhausting the stack" {
              let chain = Map.ofList [ for i in 0..199_999 -> i, [ i + 1 ] ]
              Expect.isEmpty (Relation.cyclesAmong chain) "a chain has no cycle"
              Expect.equal (Relation.terminals chain 0) (Some(Set.singleton 200_000)) "it ends at its last node"

              let ring = chain |> Map.add 199_999 [ 0 ]
              Expect.equal (Relation.cyclesAmong ring).Count 200_000 "closing it puts every node on the cycle"
          } ]

let private closure =
    testList
        "closure and chain ends"
        [ test "reachable is the reflexive-transitive closure from the sources (differential)" {
              for seed in seeds do
                  let r = randomRelation seed
                  let rng = System.Random(seed + 31)
                  let sources = nodesOf r |> Set.filter (fun _ -> rng.Next 3 = 0) |> Set.toList

                  let expected =
                      sources |> List.fold (fun acc s -> Set.union acc (reachStar r s)) Set.empty

                  Expect.equal (Relation.reachable r sources) expected (sprintf "seed %d" seed)
          }

          test "a source outside the relation is reached as itself" {
              Expect.equal
                  (Relation.reachable (Map.ofList [ 1, [ 2 ] ]) [ 9 ])
                  (Set.singleton 9)
                  "a node with no successors"
          }

          test "terminals are the successor-less nodes reached, or None when a cycle is reached (differential)" {
              for seed in seeds do
                  let r = randomRelation seed
                  let ends = Relation.terminals r

                  for n in nodesOf r do
                      Expect.equal (ends n) (refTerminals r n) (sprintf "seed %d: node %d" seed n)

                  Expect.equal (ends 10_000) (Some(Set.singleton 10_000)) "an unknown node ends at itself"
          } ]

[<Tests>]
let tests =
    testList
        "Phase 2220 - recursive questions over a finite relation, answered totally"
        [ cycles; order; linear; closure ]
