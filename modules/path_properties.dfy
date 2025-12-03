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
    if |p| == 2 {
      // Base case: PathLen(G, p) = G.EdgeWeight(p[0], p[1]) + 0
      // We know G.EdgeWeight(p[0], p[1]) >= 0 from precondition
      assert PathLen(G, p) == G.EdgeWeight(p[0], p[1]);
    } else {
      // Inductive case
      var rest := p[1..];

      // Establish preconditions for recursive call
      assert |rest| >= 1;
      assert forall i :: 0 <= i < |rest| ==> 0 <= rest[i] < G.n by {
        forall i | 0 <= i < |rest|
          ensures 0 <= rest[i] < G.n
        {
          assert rest[i] == p[i+1];
        }
      }
      assert forall i :: 0 <= i < |rest|-1 ==> G.EdgeExists(rest[i], rest[i+1]) by {
        forall i | 0 <= i < |rest|-1
          ensures G.EdgeExists(rest[i], rest[i+1])
        {
          assert rest[i] == p[i+1];
          assert rest[i+1] == p[i+2];
        }
      }
      assert forall i :: 0 <= i < |rest|-1 ==> G.EdgeWeight(rest[i], rest[i+1]) >= 0 by {
        forall i | 0 <= i < |rest|-1
          ensures G.EdgeWeight(rest[i], rest[i+1]) >= 0
        {
          assert rest[i] == p[i+1];
          assert rest[i+1] == p[i+2];
        }
      }

      // Recursive call
      PathLenNonNegative(G, rest);

      // Conclude: PathLen(G, p) = G.EdgeWeight(p[0], p[1]) + PathLen(G, rest) >= 0
      assert G.EdgeWeight(p[0], p[1]) >= 0;
      assert PathLen(G, rest) >= 0;
    }
  }


}