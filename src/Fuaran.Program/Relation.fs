namespace Fuaran.Program

/// **Recursive questions over a FINITE relation, answered totally** (Phase 2220, D47).
///
/// "Which nodes reach themselves", "which nodes does this set reach" and "where does a chain of
/// redirects end" are recursive queries: one bounded pass of the logic-tree algebra cannot state them,
/// and a recursion an author bounds by a fuel of their own choosing is exactly the general recursion the
/// charter rules out (D1). These functions are bounded by the INPUT instead: each is one traversal of
/// the relation that finishes every node once and examines every edge once, so it terminates on every
/// finite relation and its cost is linear in nodes plus edges, whatever the number of PATHS (a dense
/// diamond 200 layers deep has 4^200 of them and is answered in milliseconds). No function here takes a
/// bound, a depth or a fuel, and none recurses on the call stack, so a chain a hundred thousand long is
/// answered as a chain of ten is.
///
/// A relation is a map from a node to its successors. A successor that is not a key is a node with no
/// successors; a self-edge is an edge; a repeated successor is one edge.
///
/// **Every answer is a function of the relation's edge SET** — never of the order a successor list was
/// written in or how often an edge is repeated. Nodes are visited in ascending order and successors are
/// examined in ascending order, so a component's members, the order of the components, and every set
/// below are canonical. That is what lets a host journal or golden an answer.
///
/// These are pure, total functions of a value: they cross no wire and touch no effect. A domain's
/// expression or state witness calls them where its own vocabulary asks a recursive question.
[<RequireQualifiedAccess>]
module Relation =

    /// One traversal's dense form: the relation's nodes in ascending order, and each node's distinct
    /// successors, ascending, as indices into it.
    type private Dense<'N when 'N: comparison> =
        { Nodes: 'N[]
          Index: System.Collections.Generic.Dictionary<'N, int>
          Successors: int[][] }

    let private dense (edges: Map<'N, 'N list>) : Dense<'N> =
        let nodes =
            edges
            |> Map.fold
                (fun acc node successors -> List.fold (fun s n -> Set.add n s) (Set.add node acc) successors)
                Set.empty
            |> Set.toArray

        let index =
            System.Collections.Generic.Dictionary<'N, int>(nodes.Length, HashIdentity.Structural)

        nodes |> Array.iteri (fun i node -> index[node] <- i)

        let successors =
            nodes
            |> Array.map (fun node ->
                match Map.tryFind node edges with
                | None
                | Some [] -> [||]
                | Some targets ->
                    targets
                    |> List.map (fun t -> index[t])
                    |> List.distinct
                    |> List.sort
                    |> List.toArray)

        { Nodes = nodes
          Index = index
          Successors = successors }

    /// What one strongly-connected-components pass found: the components as index arrays, in the order the
    /// pass finished them (every component after each component it reaches), and which node lies in which.
    type private Pass =
        {
            Components: int[] list
            ComponentOf: int[]
            /// Nodes finished plus edges examined — the pass's whole work, which the linearity law reads.
            Work: int
        }

    /// Tarjan's pass, iterative: an explicit frame stack in place of the call stack, so depth costs heap,
    /// not stack. Each node is finished once and each edge examined once.
    let private pass (graph: Dense<'N>) : Pass =
        let n = graph.Nodes.Length
        let order = Array.create n -1
        let low = Array.zeroCreate<int> n
        let onStack = Array.zeroCreate<bool> n
        let componentOf = Array.create n -1
        let stack = System.Collections.Generic.Stack<int>()
        let frames = System.Collections.Generic.Stack<int * int>()
        let mutable next = 0
        let mutable work = 0
        let mutable components = []
        let mutable count = 0

        let enter v =
            order[v] <- next
            low[v] <- next
            next <- next + 1
            stack.Push v
            onStack[v] <- true
            frames.Push(v, 0)

        for root in 0 .. n - 1 do
            if order[root] < 0 then
                enter root

                while frames.Count > 0 do
                    let v, i = frames.Pop()
                    let successors = graph.Successors[v]

                    if i < successors.Length then
                        frames.Push(v, i + 1)
                        work <- work + 1
                        let w = successors[i]

                        if order[w] < 0 then
                            enter w
                        elif onStack[w] then
                            low[v] <- min low[v] order[w]
                    else
                        work <- work + 1

                        if low[v] = order[v] then
                            let members = ResizeArray<int>()
                            let mutable w = -1

                            while w <> v do
                                w <- stack.Pop()
                                onStack[w] <- false
                                componentOf[w] <- count
                                members.Add w

                            members.Sort()
                            components <- members.ToArray() :: components
                            count <- count + 1

                        if frames.Count > 0 then
                            let u, j = frames.Pop()
                            low[u] <- min low[u] low[v]
                            frames.Push(u, j)

        { Components = List.rev components
          ComponentOf = componentOf
          Work = work }

    /// Whether a component is a CYCLE: more than one member, or one member with an edge to itself.
    let private isCycle (graph: Dense<'N>) (members: int[]) =
        members.Length > 1 || Array.contains members[0] graph.Successors[members[0]]

    /// The pass's work over `edges` — nodes finished plus edges examined, after repeated successors are
    /// merged. Exposed to this assembly's laws only: it is the counted evidence that the cost is linear.
    let internal work (edges: Map<'N, 'N list>) : int = pass (dense edges) |> _.Work

    /// **Every strongly-connected component of the relation**, singletons included: each component's
    /// members ascending, and the components in REVERSE TOPOLOGICAL order — a component comes after every
    /// component it reaches, so over a "depends on" relation dependencies come first. Among components
    /// neither of which reaches the other, the order is the pass's over ascending nodes, which is a
    /// function of the edge set alone.
    let components (edges: Map<'N, 'N list>) : 'N list list =
        let graph = dense edges

        pass graph
        |> _.Components
        |> List.map (fun members -> members |> Array.map (fun i -> graph.Nodes[i]) |> List.ofArray)

    /// The components that are CYCLES — more than one member, or a single member with a self-edge — in
    /// `components`' order. Every cycle of the relation lies inside exactly one of them.
    let cycles (edges: Map<'N, 'N list>) : 'N list list =
        let graph = dense edges

        pass graph
        |> _.Components
        |> List.filter (isCycle graph)
        |> List.map (fun members -> members |> Array.map (fun i -> graph.Nodes[i]) |> List.ofArray)

    /// **Every node on a cycle** — the nodes that reach themselves by one edge or more. The same answer,
    /// node for node, as roadmap-engine#752's `cyclesAmong` over the same map.
    let cyclesAmong (edges: Map<'N, 'N list>) : Set<'N> =
        cycles edges |> List.concat |> Set.ofList

    /// **The closure of the relation from `sources`**: every node reachable from one of them by zero edges
    /// or more — the sources themselves included, a source that is no node of the relation included as a
    /// node with no successors.
    let reachable (edges: Map<'N, 'N list>) (sources: 'N seq) : Set<'N> =
        let graph = dense edges
        let seen = Array.zeroCreate<bool> graph.Nodes.Length
        let frontier = System.Collections.Generic.Stack<int>()
        let mutable outside = Set.empty

        for source in sources do
            match graph.Index.TryGetValue source with
            | true, i when not seen[i] ->
                seen[i] <- true
                frontier.Push i
            | true, _ -> ()
            | false, _ -> outside <- Set.add source outside

        while frontier.Count > 0 do
            for w in graph.Successors[frontier.Pop()] do
                if not seen[w] then
                    seen[w] <- true
                    frontier.Push w

        graph.Nodes
        |> Array.indexed
        |> Array.fold (fun acc (i, node) -> if seen[i] then Set.add node acc else acc) outside

    /// **Where a node's chains END**: the terminal nodes — nodes with no successor — it reaches, itself
    /// when it has none, or `None` when it reaches a CYCLE, because a chain that loops ends nowhere. A node
    /// that is no node of the relation ends at itself. Partially applied, one pass answers every node.
    ///
    /// Over a "carried into" relation (a superseded item's successors) this is the set of items that
    /// finally carry a node's work, and `None` is the loop that leaves it carried by nothing: readiness
    /// over redirects is "every terminal shipped" with no further machinery.
    let terminals (edges: Map<'N, 'N list>) : 'N -> Set<'N> option =
        let graph = dense edges
        let found = pass graph
        let ends = Array.create<Set<'N> option> graph.Nodes.Length None

        // Reverse topological order: every component a component reaches was answered before it.
        for members in found.Components do
            let answer =
                if isCycle graph members then
                    None
                else
                    let v = members[0]

                    match graph.Successors[v] with
                    | [||] -> Some(Set.singleton graph.Nodes[v])
                    | successors ->
                        successors
                        |> Array.fold
                            (fun acc w ->
                                match acc, ends[w] with
                                | Some sofar, Some theirs -> Some(Set.union sofar theirs)
                                | _ -> None)
                            (Some Set.empty)

            for v in members do
                ends[v] <- answer

        fun node ->
            match graph.Index.TryGetValue node with
            | true, i -> ends[i]
            | false, _ -> Some(Set.singleton node)
