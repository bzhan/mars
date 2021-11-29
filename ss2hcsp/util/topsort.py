"""Topological sort"""

class TopologicalSortException(Exception):
    def __init__(self, cycle):
        self.cycle = cycle


def topological_sort(graph):
    """Given a graph stored as adjacency lists, return topological
    order of vertices, or return an error if there is a cycle.
    
    """
    # Form the reverse graph
    rev_graph = dict()
    for v in graph:
        rev_graph[v] = list()
    for v, edges in graph.items():
        for edge in edges:
            rev_graph[edge].append(v)

    # List of roots (no vertices depend on them)
    roots = list()
    for v in graph:
        if len(rev_graph[v]) == 0:
            roots.append(v)

    # Contains topological order
    topo_sort = []

    # Whether a node is explored
    explored = dict()
    for v in graph:
        explored[v] = False

    # Temporary path
    path = []

    def dfs(v):
        for next in graph[v]:
            if next in path:
                # Back-edge, found a loop
                raise TopologicalSortException(path[path.index(next):])
            elif explored[next]:
                # Already explored
                continue
            else:
                # Never explored
                path.append(next)
                explored[next] = True
                dfs(next)
                del path[-1]
        topo_sort.append(v)
    
    for root in roots:
        dfs(root)

    if len(topo_sort) == len(graph):
        return topo_sort
    else:
        for v in graph:
            if not explored[v]:
                dfs(v)  # Must find cycle and raise exception
