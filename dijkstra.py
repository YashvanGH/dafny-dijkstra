import heapq
import sys
from graph import Graph
from typing import List

def dijkstra(graph: Graph, source: int):
    # TODO: Implement Dijkstra's Algorithm
    n = graph.n
    prev = [-1] * n # Stores predecessor of each node on shortest path

    dist = [sys.maxsize] * n
    dist[source] = 0

    pq = []
    heapq.heappush(pq, (0, source))

    while pq:
        d_u, u = heapq.heappop(pq)

        for v, w in graph.adj[u]:
            if dist[v] > d_u + w:
                dist[v] = d_u + w
                prev[v] = u
                heapq.heappush(pq, (dist[v], v))

    return dist, prev
                
def reconstruct_path(source: int, target: int, prev: List[int]) -> List[int]:
    # Unreachable target
    if prev[target] is None and target != source and prev[target] != -1:
        return []  # no path
    
    path = []
    curr = target
    while curr != -1:
        path.append(curr)
        curr = prev[curr]
    path.reverse()
    return path

def print_all_paths(source: int, dist: List[int], prev: List[int]):
    for v in range(len(dist)):
        path = reconstruct_path(source, v, prev)
        if not path:
            print(f"{source} -> {v}: no path")
        else:
            path_str = " -> ".join(map(str, path))
            print(f"Path from {source} -> {v}: {path_str}  (dist = {dist[v]})")

    
if __name__ == "__main__":
    g = Graph(5)
    g.add_edge(0, 1, 10)    # 0 -> 1 (weight 10)
    g.add_edge(0, 4, 5)     # 0 -> 4 (weight 5)
    g.add_edge(1, 2, 1)     # 1 -> 2 (weight 1)
    g.add_edge(1, 4, 2)     # 1 -> 4 (weight 2)
    g.add_edge(2, 3, 4)     # 2 -> 3 (weight 4)
    g.add_edge(3, 0, 7)     # 3 -> 0 (weight 7)
    g.add_edge(4, 1, 3)     # 4 -> 1 (weight 3)
    g.add_edge(4, 2, 9)     # 4 -> 2 (weight 9)
    g.add_edge(4, 3, 2)     # 4 -> 3 (weight 2)

    dist, prev = dijkstra(g, 0)
    print_all_paths(0, dist, prev)