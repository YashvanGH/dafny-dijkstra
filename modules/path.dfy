include "graph.dfy"

module Path 
{
    import opened Graph

    predicate ValidPath(G: Graph, src: int, dst: int, p: seq<int>)
        requires G.WellFormed()
        requires 0 <= src < G.n && 0 <= dst < G.n
        //requires forall i :: 0 <= i < |p| ==> 0 <= p[i] < G.n 
        reads G, G.adj

    {
        |p| > 0 &&
        p[0] == src &&
        p[|p| - 1] == dst &&

        // Every vertex must be in range
        forall i :: 0 <= i < |p| ==> 
            0 <= p[i] < G.n &&
            // And if it's not the last index, the edge must exist
            (i+1 < |p| ==> 0 <= p[i+1] < G.n && G.EdgeExists(p[i], p[i+1]))
    }

    function PathLen(G: Graph, p: seq<int>): int
        requires G.WellFormed()
        requires forall i :: 0 <= i < |p| ==> 0 <= p[i] < G.n
        requires forall i :: 0 <= i < |p| - 1 ==> G.EdgeExists(p[i], p[i+1])
        reads G, G.adj
        decreases p
    {
        if |p| <= 1 then
        0
        else
        G.EdgeWeight(p[0], p[1]) + PathLen(G, p[1..])
    }
    
    ghost predicate Reachable(G: Graph, src: int, v: int)
        requires G.WellFormed()
        requires 0 <= src < G.n && 0 <= v < G.n
        reads G, G.adj
    {
        exists p: seq<int> :: ValidPath(G, src, v, p)
    }
}