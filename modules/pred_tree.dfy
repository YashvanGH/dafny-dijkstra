include "graph.dfy"
include "path.dfy"

module PredTree {
    import opened Graph
    import opened Path

    predicate PredChainReachesSrc(pred: array<int>, src: int, v: int, fuel: nat)
        requires 0 <= src < pred.Length && 0 <= v < pred.Length
        reads pred
        decreases fuel
    {
        if fuel == 0 then
            false
        else if v == src then
            true
        else if pred[v] < 0 || pred[v] >= pred.Length then
            false
        else
            PredChainReachesSrc(pred, src, pred[v], fuel - 1)
    }

    function ReconstructPath(pred: array<int>, src: int, v: int, fuel: nat): seq<int>
        requires 0 <= src < pred.Length && 0 <= v < pred.Length
        reads pred
        decreases fuel
    {
        if fuel == 0 || v == src then
            [v]
        else if pred[v] < 0 then
            [v]
        else if 0 <= pred[v] < pred.Length then
            ReconstructPath(pred, src, pred[v], fuel - 1) + [v]
        else
            [v]
    }

    lemma {:induction fuel} PredChainEventuallyReachesSrcFuel(G: Graph, src: int, v: int, pred: array<int>, fuel: nat)
        requires G.WellFormed()
        requires 0 <= src < G.n && 0 <= v < G.n
        requires pred.Length == G.n
        requires pred[src] == -1
        requires forall u :: 0 <= u < G.n && pred[u] >= 0 ==>
                               0 <= pred[u] < G.n && G.EdgeExists(pred[u], u)
        requires PredChainReachesSrc(pred, src, v, fuel)
        ensures Reachable(G, src, v)
        decreases fuel
    {
        if v == src {
            ReachableRefl(G, src);
        } else {
            var parent := pred[v];
            PredChainEventuallyReachesSrcFuel(G, src, parent, pred, fuel - 1);
            ReachableTrans(G, src, parent, v);
        }
    }

    // Wrapper
    lemma PredChainEventuallyReachesSrc(G: Graph, src: int, v: int, pred: array<int>)
        requires G.WellFormed()
        requires 0 <= src < G.n && 0 <= v < G.n
        requires pred.Length == G.n
        requires pred[src] == -1
        requires forall u :: 0 <= u < G.n && pred[u] >= 0 ==>
                               0 <= pred[u] < G.n && G.EdgeExists(pred[u], u)
        requires forall u :: 0 <= u < G.n && u != src ==>
                               (pred[u] >= 0 || pred[u] == -1)
        // predecessor chain from v reaches src
        requires PredChainReachesSrc(pred, src, v, G.n)
        ensures Reachable(G, src, v)
    {
        PredChainEventuallyReachesSrcFuel(G, src, v, pred, G.n);
    }

    // Helper lemma: reflexivity of reachability
    lemma ReachableRefl(G: Graph, v: int)
        requires G.WellFormed()
        requires 0 <= v < G.n
        ensures Reachable(G, v, v)
    {
        var path := [v];
        assert ValidPath(G, v, v, path);
        assert |path| > 0 && path[0] == v && path[|path| - 1] == v;
    }

    lemma ReachableTrans(G: Graph, a: int, b: int, c: int)
        requires G.WellFormed()
        requires 0 <= a < G.n && 0 <= b < G.n && 0 <= c < G.n
        requires Reachable(G, a, b)
        requires G.EdgeExists(b, c)
        ensures Reachable(G, a, c)
    {
        var pathAB :| ValidPath(G, a, b, pathAB);
        var pathAC := pathAB + [c];
        assert ValidPath(G, a, c, pathAC);
    }
}
