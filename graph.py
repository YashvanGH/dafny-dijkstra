class Graph:
    # TODO: Implement Graph Representation (Using adjacency lists)
    def __init__(self, n):
        """
        Initialises new graph object

        Args:
            n: The number of nodes in the graph labelled [0, n-1]
            adj: Adjacency list to store edges and respective edge weights of nodes
        """
        self.n = n
        self.adj = [[] for _ in range(n)]

    def add_edge(self, u, v, w):
        """
        Adds an edge to the graph

        Args:
            u and v: An edge will be created from node u to v
            w: Weight of the created edge
        """
        self.adj[u].append((v, w))
