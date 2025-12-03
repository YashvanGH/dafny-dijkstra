include "graph.dfy"
include "path.dfy"

module PathProperties {
  import opened Graph
  import opened Path

  lemma PathLenNonNegative(G: Graph, p: seq<int>)
    requires G.WellFormed()
    requires |p| >= 2
    requires forall i :: 0 <= i < |p| ==> 0 <= p[i] < G.n
    requires forall i :: 0 <= i < |p|-1 ==> G.EdgeExists(p[i], p[i+1])
    requires forall i :: 0 <= i < |p|-1 ==> G.EdgeWeight(p[i], p[i+1]) >= 0
    ensures PathLen(G, p) >= 0
    decreases |p|
  {
    if |p| > 2 {
      PathLenNonNegative(G, p[1..]);
    }
  }
}