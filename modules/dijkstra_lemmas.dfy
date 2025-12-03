include "graph.dfy"
include "path.dfy"
include "shortest_spec.dfy"

module DijkstraLemmas {
  import opened Graph
  import opened Path
  import opened ShortestSpec

  lemma DistancesNeverDecrease(distOld: seq<int>, distNew: seq<int>, v: int)
    requires 0 <= v < |distOld|
    requires |distOld| == |distNew|
    requires forall x :: 0 <= x < |distOld| ==> distNew[x] >= 0
    requires forall x :: 0 <= x < |distOld| ==> distOld[x] <= distNew[x]
    ensures distOld[v] <= distNew[v]
  {
  }

  lemma RelaxationCorrect(G: Graph, u: int, v: int, distU: int)
    requires G.WellFormed()
    requires 0 <= u < G.n && 0 <= v < G.n
    requires G.EdgeExists(u, v)
    requires distU >= 0
    requires G.EdgeWeight(u, v) >= 0
    ensures distU + G.EdgeWeight(u, v) >= distU
  {
  }

  predicate HasMinimalDistance(dist: seq<int>, visited: set<int>, u: int)
    requires 0 <= u < |dist|
  {
    u !in visited && forall x :: 0 <= x < |dist| && x !in visited ==> dist[u] <= dist[x]
  }

  lemma ChoosingMinimalU_is_Safe(dist: seq<int>, visited: set<int>, u: int)
    requires 0 <= u < |dist|
    requires HasMinimalDistance(dist, visited, u)
    ensures forall x :: 0 <= x < |dist| && x !in visited ==> dist[u] <= dist[x]
  {
  }
}