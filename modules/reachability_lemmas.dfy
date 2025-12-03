include "graph.dfy"
include "path.dfy"

module ReachabilityLemmas {
    import opened Graph
    import opened Path

    lemma ReachableImpliesNonEmptyPath(G: Graph, src: int, v: int)
        requires G.WellFormed()
        requires 0 <= src < G.n && 0 <= v < G.n
        requires Reachable(G, src, v)
        ensures exists p :: ValidPath(G, src, v, p) && |p| > 0
    {
        var p :| ValidPath(G, src, v, p);
    }

    lemma ReachabilityIsPrefixClosed(G: Graph, src: int, v: int, p: seq<int>)
        requires G.WellFormed()
        requires 0 <= src < G.n && 0 <= v < G.n
        requires |p| > 0
        requires ValidPath(G, src, v, p)
        ensures forall i :: 0 <= i < |p| ==> Reachable(G, src, p[i])
    {
        forall i | 0 <= i < |p|
            ensures Reachable(G, src, p[i])
        {
            var prefix := p[..i+1];
            assert ValidPath(G, src, p[i], prefix);
        }
    }

    lemma ExtendPathMaintainsValidity(G: Graph, src: int, u: int, v: int, p: seq<int>)
        requires G.WellFormed()
        requires 0 <= src < G.n && 0 <= u < G.n && 0 <= v < G.n
        requires |p| > 0
        requires ValidPath(G, src, u, p)
        requires p[|p|-1] == u
        requires G.EdgeExists(u, v)
        ensures ValidPath(G, src, v, p + [v])
    {
        var q := p + [v];
        assert q[0] == src;
        assert q[|q| - 1] == v;
        assert forall i :: 0 <= i < |q| ==> 0 <= q[i] < G.n;
        assert forall i :: 0 <= i < |q| - 1 ==> G.EdgeExists(q[i], q[i+1]);
    }
}
