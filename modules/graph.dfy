module Graph 
{
    
    const INF: int := 1000000

    datatype Edge = Edge(to: int, w: int)

    class Graph {
        const n: nat
        const adj: array<seq<Edge>>

        predicate WellFormed()
            reads this, adj
        {
            adj != null &&
            adj.Length == n &&
            forall v :: 0 <= v < n ==>
                forall e :: e in adj[v] ==>
                    0 <= e.to < n && 0 <= e.w
        }

        predicate EdgeExists(u: int, v: int)
            requires WellFormed()
            requires 0 <= u < n && 0 <= v < n
            reads this, adj
        {
            EdgeWeight(u, v) != INF 
        }

        function EdgeWeight(u: int, v: int): int
            requires WellFormed()
            requires 0 <= u < n && 0 <= v < n
            reads this, adj
        {
            SeqEdgeWeight(adj[u], v)
        }

        // Look up weight of edge to v in a sequence of edges.
        // Returns INF if no such edge.
        function SeqEdgeWeight(s: seq<Edge>, v: int): int
            decreases s
        {
            if |s| == 0 then
                INF
            else if s[0].to == v then
                s[0].w
            else
                SeqEdgeWeight(s[1..], v)
        }
    }
}

