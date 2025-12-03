include "graph.dfy"
include "path.dfy"
include "shortest_spec.dfy"

module Dijkstra
{
  import opened Graph
  import opened Path
  import opened ShortestSpec

  const INF: int := 1000000

  method Dijkstra(G: Graph, src: int) returns (dist: array<int>, pred: array<int>)
    requires G.WellFormed()
    requires 0 <= src < G.n
    ensures ShortestSpec.ShortestDistances(G, src, dist)
    ensures ShortestSpec.ShortestTree(G, src, dist, pred)

  {
    dist := new int[G.n];
    pred := new int[G.n];

    // Initialise all distances to INF and preds to -1
    var i := 0;
    while i < G.n
      invariant 0 <= i <= G.n
      invariant dist != null && dist.Length == G.n
      invariant pred != null && pred.Length == G.n
      invariant forall v :: 0 <= v < i ==> dist[v] == INF && pred[v] == -1
    {
      dist[i] := INF;
      pred[i] := -1;
      i := i + 1;
    }

    dist[src] := 0;

    var visited: set<int> := {};
    var k: int := 0;

    while k < G.n
      invariant 0 <= k <= G.n
      invariant visited <= set v | 0 <= v < G.n
      invariant |visited| == k
      invariant dist != null && dist.Length == G.n
      invariant pred != null && pred.Length == G.n
      // 1. Every visited node has its final shortest distance
      invariant forall u :: u in visited ==>
                              Path.Reachable(G, src, u) &&
                              (exists p: seq<int> ::
                                 Path.ValidPath(G, src, u, p) &&
                                 dist[u] == Path.PathLen(G, p)) &&
                              (forall q: seq<int> ::
                                 Path.ValidPath(G, src, u, q) ==>
                                   dist[u] <= Path.PathLen(G, q))

      // 2. For edges out of visited nodes, dist is an upper bound
      invariant forall u, v :: u in visited &&
                               0 <= v < G.n &&
                               G.EdgeExists(u, v) ==>
                                 dist[v] <= dist[u] + G.EdgeWeight(u, v)

      // 3. Distances are non-negative and src is 0
      invariant forall v :: 0 <= v < G.n ==> dist[v] >= 0
      invariant dist[src] == 0

      decreases G.n - k
    {
      // --- Choose vertex with minimal distance i.e. dist[u] ---
      var u := -1;
      var best := INF;
      i := 0;
      while i < G.n
        invariant 0 <= i <= G.n
        invariant (u == -1 || 0 <= u < G.n)
        invariant (u == -1 ==> best == INF)
        invariant forall v :: 0 <= v < i && v !in visited ==> dist[v] >= best
      {
        if i !in visited && dist[i] < best {
          best := dist[i];
          u := i;
        }
        i := i + 1;
      }

      if u == -1 || best == INF {
        k := G.n;   // nothing more reachable
      } else {
        visited := visited + {u};

        // --- relax edges from u ---
        var j := 0;
        while j < |G.adj[u]|
          invariant 0 <= j <= |G.adj[u]|
        {
          var e := G.adj[u][j];
          if dist[u] + e.w < dist[e.to] {
            dist[e.to] := dist[u] + e.w;
            pred[e.to] := u;
          }
          j := j + 1;
        }

        k := k + 1;
      }
    }
  }
}