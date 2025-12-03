include "graph.dfy"
include "path.dfy"

module ShortestSpec 
{
    import opened Graph
    import opened Path

    const INF: int := 1000000

    // Distance encodes true shortest path distances from src
    ghost predicate ShortestDistances(G: Graph, src: int, dist: array<int>)
        requires G.WellFormed()
        requires 0 <= src < G.n
        reads G, G.adj, dist

    {
        dist != null &&
        dist.Length == G.n &&
        dist[src] == 0 &&

        // Non-negativity - technically not needed here but just for clarity
        forall v :: 0 <= v < G.n ==> dist[v] >= 0 &&

        // Every vertex is either reachable with minimal distance or set to INF i.e. unreachable
        forall v :: 0 <= v < G.n ==>
        (
            // Reachable => dist[v] is finite and equals minimum path length
            Path.Reachable(G, src, v) ==>
                dist[v] < INF &&
                (exists p ::
                    Path.ValidPath(G, src, v, p) &&
                    dist[v] == Path.PathLen(G, p)) &&
                (forall q ::
                    Path.ValidPath(G, src, v, q) ==>
                        dist[v] <= Path.PathLen(G, q))
        ) &&
        (
            // Unreachable => dist[v] = INF
            !Path.Reachable(G, src, v) ==> dist[v] == INF
        )
    }

    // Predecessor array (pred) encodes a shortest-path tree consistent with dist
    ghost predicate ShortestTree(G: Graph, src: int, dist: array<int>, pred: array<int>)
        requires G.WellFormed()
        requires 0 <= src < G.n
        requires dist != null && dist.Length == G.n
        reads G, G.adj, dist, pred

    {
        pred != null &&
        pred.Length == G.n &&
        
        // src is root hence no pred
        pred[src] == -1 &&

        // Every node has a (reasonable) predecessor
        forall v :: 0 <= v < G.n && v != src ==>
        if Path.Reachable(G, src, v) then
            // Reachable vertices have a real predecessor on a shortest edge
            0 <= pred[v] < G.n &&
            G.EdgeExists(pred[v], v) &&
            dist[v] == dist[pred[v]] + G.EdgeWeight(pred[v], v) &&
            // strictly decreasing along preds => no cycles
            dist[pred[v]] < dist[v]          
        else
            // Unreachable vertices just use -1
            pred[v] == -1
    }
}