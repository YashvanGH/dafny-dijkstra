include "graph.dfy"
include "path.dfy"

module PredTree {
  import opened Graph
  import opened Path

  // Predicate to check if following predecessors from v eventually reaches src
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

  // Helper function to reconstruct path from predecessor tree
  function ReconstructPath(pred: array<int>, src: int, v: int, fuel: nat): seq<int>
    requires 0 <= src < pred.Length && 0 <= v < pred.Length
    reads pred
    decreases fuel
  {
    if fuel == 0 || v == src then
      [v]
    else if pred[v] < 0 then
      [v]  // No predecessor, stop here
    else if 0 <= pred[v] < pred.Length then
      ReconstructPath(pred, src, pred[v], fuel - 1) + [v]
    else
      [v]  // Invalid predecessor
  }

  // Main lemma: predecessor chain implies reachability
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
      // Base case: v is the source, so it's trivially reachable
      ReachableRefl(G, src);
    } else {
      // Recursive case: follow predecessor
      var parent := pred[v];
      assert 0 <= parent < G.n;
      assert G.EdgeExists(parent, v);

      // By definition of PredChainReachesSrc, parent also reaches src with less fuel
      PredChainEventuallyReachesSrcFuel(G, src, parent, pred, fuel - 1);

      // Now we have: Reachable(G, src, parent)
      // And we have: G.EdgeExists(parent, v)
      // Therefore: Reachable(G, src, v)

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

  // Helper lemma: transitivity through one edge
  lemma ReachableTrans(G: Graph, a: int, b: int, c: int)
    requires G.WellFormed()
    requires 0 <= a < G.n && 0 <= b < G.n && 0 <= c < G.n
    requires Reachable(G, a, b)
    requires G.EdgeExists(b, c)
    ensures Reachable(G, a, c)
  {
    // There exists a path from a to b
    var pathAB :| ValidPath(G, a, b, pathAB) &&
                  |pathAB| > 0 &&
                  pathAB[0] == a &&
                  pathAB[|pathAB| - 1] == b;

    // Extend the path with the edge to c
    var pathAC := pathAB + [c];

    // Prove pathAC is valid
    assert ValidPath(G, a, c, pathAC);
    assert pathAC[0] == a && pathAC[|pathAC| - 1] == c;
  }
}