import glob
import heapq
import argparse
import os
from collections import deque


def ReadPrimalFromFile(filePath: str):
    with open(filePath, "r") as f:
        f.readline()
        n, r = map(int, f.readline().split())
        G = [[] for _ in range(n)]
        degree = [0 for _ in range(n)]
        for i in range(r):
            G[i].append((i + 1) % r)
            G[(i + 1) % r].append(i)
        for i in range(n-r):
            v, d, *us = map(int, f.readline().split())
            v -= 1
            degree[v] = d
            for u in us:
                u -= 1
                G[v].append(u)
                if u < r:
                    G[u].append(v)
        return n, r, G, degree
    assert False


# 
def LabelEdges(n:int, r: int, G: "list[list[int]]"):
    edges = set()
    for i in range(n):
        for j in G[i]:
            edges.add((i, j))
    def is3Cycle(i: int, j: int, k: int):
        return (i, j) in edges and (j, k) in edges and (k, i) in edges
    triangles = set()
    for i in range(n):
        for j in range(i):
            for k in range(j):
                if is3Cycle(k, j, i):
                    triangles.add((k, j, i))
    triangles = sorted(list(triangles))
    edgeIndexes = {}
    def addEdge(x, y):
        if x > y: x, y = y, x
        if (x, y) not in edgeIndexes:
            edgeIndexes[(x, y)] = len(edgeIndexes)
    for i in range(r):
        addEdge(i, (i + 1) % r)
    for a,b,c in triangles:
        addEdge(a, b)
        addEdge(b, c)
        addEdge(c, a)
    return edgeIndexes


# contEdges の辺を距離にカウントしないような最短経路を求める。
def WF(n: int, r: int, G: list, contEdges: list, edgeIndexes: dict):
    dist = [[300 for _ in range(n)] for _ in range(n)]
    for i in range(n):
        dist[i][i] = 0
    for v in range(n):
        for u in G[v]:
            if v < u:
                assert (v, u) in edgeIndexes
                idx = edgeIndexes[(v, u)]
                if str(idx) in contEdges:
                    dist[v][u] = 0
                    dist[u][v] = 0
                else:
                    dist[v][u] = 1
                    dist[u][v] = 1
    
    for k in range(n):
        for i in range(n):
            for j in range(n):
                dist[i][j] = min(dist[i][k] + dist[k][j], dist[i][j])
    return dist

# s から t の長さ 4 以下のパスを列挙する
def allPaths(n: int, G: list, s: int, t: int):
    paths = []
    def dfs(v, path):
        path.append(v)
        if path[-1] == t:
            paths.append(path.copy())
            path.pop()
            return
        if len(path) == 5:
            path.pop()
            return
        for u in G[v]:
            if u not in path:
                dfs(u, path)
        path.pop()
        return
    path = []
    dfs(s, path)
    return paths


# グラフ G 上で s から t の最短経路を列挙する。 
def shortestPaths(n: int, G: list, s: int, t: int):
    dist = [1000 for _ in range(n)]
    dist[s] = 0

    heap = []
    heapq.heappush(heap, (0, s))
    while heap:
        d, v = heapq.heappop(heap)
        for u in G[v]:
            if dist[v] + 1 < dist[u]:
                dist[u] = dist[v] + 1
                heapq.heappush(heap, (dist[u], u))

    paths = [[] for _ in range(n)]
    paths[s].append([s])

    heapq.heappush(heap, s)
    while heap:
        v = heapq.heappop(heap)
        for u in G[v]:
            if dist[u] == dist[v] + 1:
                paths[u].extend([path + [u] for path in paths[v]])
                heapq.heappush(heap, u)
    
    unique_paths = []
    for path in paths[t]:
        if path in unique_paths:
            continue
        unique_paths.append(path)
    return unique_paths


def getComponent(n, r, G, pqpath):
    p = pqpath[0]
    q = pqpath[-1]
    assert p != q and p < r and q < r

    cutset = set()
    for v in pqpath:
        cutset.add(v)

    component_id = [-1 for _ in range(n)]
    component = []
    def dfs(v, c):
        if v in cutset or component_id[v] != -1:
            return
        component_id[v] = c
        component.append(v)
        for u in G[v]:
            dfs(u, c)
        return
    
    v = (p + 1) % r
    while v != q:
        dfs(v, 0)
        v = (v + 1) % r

    return component


def getComponent1(n, r, G, p1q1_path, p2q2_path):
    component2 = set()
    for v in getComponent(n, r, G, p1q1_path):
        component2.add(v)
    
    q2p2_path = list(reversed(p2q2_path))
    component = []
    for v in getComponent(n, r, G, q2p2_path):
        if v not in component2:
            component.append(v)
    return component


def getComponent2(n, r, G, p1q1_path, p2q2_path):
    component2 = set()
    for v in getComponent(n, r, G, p1q1_path):
        component2.add(v)

    component = []
    for v in getComponent(n, r, G, p2q2_path):
        if v in component2:
            component2.remove(v)
            continue
        component.append(v)

    for v in component2:
        component.append(v)

    return component


def sizeOfVertices(r, component):
    s = 0
    t = 0
    for v in component:
        if v < r:
            s += 1
        else:
            t += 1
    return (s, t)


# a,b,c,d は ring にその順に並んでいる頂点
# dist[a][b] = d0
# dist[c][d] = d1
def find_ab_cd(d0, d1, n, r, contract_dist):
    abcds = []
    for a in range(r):
        for b in range(a+1, r):
            if contract_dist[a][b] == d0:
                for c in range(b+1, a+r):
                    for d in range(c+1, a+r):
                        if contract_dist[c%r][d%r] == d1:
                            abcds.append((a, b, c%r, d%r))
                for c in range(a+1, b):
                    for d in range(c+1, b):
                        if contract_dist[c][d] == d1:
                            abcds.append((b, a, c, d))
    return abcds


# 頂点数 n, リングサイズ r の configuration G の
# リング上の頂点 p, q を同一視させてできる annular island を出力する。
def gen_annular_island(n, r, G, p, q):
    assert p < r and q < r
    if p > q:
        p, q = q, p

    edges = set()
    for i in range(n):
        for j in G[i]:
            edges.add((i, j))
    
    edgeIndexes = {}
    def addEdge(x, y):
        if x > y: x, y = y, x
        if (x, y) not in edgeIndexes:
            edgeIndexes[(x, y)] = len(edgeIndexes)

    # make index such that edges make annular island
    for v in range(p, q):
        addEdge(v, v+1)
    v = p
    while v != q:
        addEdge(v, (v + r - 1) % r)
        if v == 0:
            v = r - 1
        else:
            v -= 1
    
    # enumerate triangle
    def is3Cycle(i: int, j: int, k: int):
        return (i, j) in edges and (j, k) in edges and (k, i) in edges
    triangles = set()
    for i in range(n):
        for j in range(i):
            for k in range(j):
                if is3Cycle(k, j, i):
                    addEdge(k, j)
                    addEdge(k, i)
                    addEdge(j, i)
                    kj = edgeIndexes[(k, j)]
                    ki = edgeIndexes[(k, i)]    
                    ji = edgeIndexes[(j, i)]
                    triangles.add((kj, ki, ji))
    
    # generate
    txt = f"{len(triangles)} {q-p} {r-(q-p)}\n"
    for a, b, c in triangles:
        txt += f"{a} {b} {c}\n"

    return txt


def output(content, filepath):
    with open(filepath, mode='w') as f:
        f.write(content)
    return


def dist00(n, r, G, dist, contract_dist, confname, outdir):
    ab0_cd0s = find_ab_cd(0, 0, n, r, contract_dist)
    for a, b, c, d in ab0_cd0s:
        abpaths = allPaths(n, G, a, b)
        bcpaths = allPaths(n, G, b, c)
        cdpaths = allPaths(n, G, c, d)
        dapaths = allPaths(n, G, d, a)
        oneedge_contractible = True
        oneedge_noncontractible = True
        for abpath in abpaths:
            for cdpath in cdpaths:
                component1 = getComponent1(n, r, G, abpath, cdpath)
                component2 = getComponent2(n, r, G, abpath, cdpath)
                s1, t1 = sizeOfVertices(r, component1)
                s2, t2 = sizeOfVertices(r, component2)
                size1 = (s1 + 1) // 2 + t1
                size2 = (s2 + 1) // 2 + t2
                l1 = len(abpath) - 1
                l2 = len(cdpath) - 1
                # contractible cycle
                if (l1 + l2 + 1 <= 4 and min(size1, size2) > 0) or (l1 + l2 + 1 == 5 and min(size1, size2) > 1):
                    oneedge_contractible = False
                # annulus cut
                if (l1 + l2 + 1 <= 4 and min(size1, size2) > 0) or (l1 == 2 and l2 == 2 and min(size1, size2) > 1):
                    oneedge_noncontractible = False
        for bcpath in bcpaths:
            for dapath in dapaths:
                component1 = getComponent1(n, r, G, bcpath, dapath)
                component2 = getComponent2(n, r, G, bcpath, dapath)
                s1, t1 = sizeOfVertices(r, component1)
                s2, t2 = sizeOfVertices(r, component2)
                size1 = (s1 + 1) // 2 + t1
                size2 = (s2 + 1) // 2 + t2
                l1 = len(bcpath) - 1
                l2 = len(dapath) - 1
                # annulus cut
                if (l1 + l2 + 1 <= 4 and min(size1, size2) > 0) or (l1 == 2 and l2 == 2 and min(size1, size2) > 1):
                    oneedge_contractible = False
                # contractible cycle
                if (l1 + l2 + 1 <= 4 and min(size1, size2) > 0) or (l1 + l2 + 1 == 5 and min(size1, size2) > 1):
                    oneedge_noncontractible = False
        if oneedge_contractible:
            print(f"contractible, 00-onedge, a, b, c, d: {a, b, c, d} in {confname}")
            G_ad = gen_annular_island(n, r, G, a, d)
            G_bc = gen_annular_island(n, r, G, b, c)
            output(G_ad, os.path.join(outdir, f"{confname}_contractible_00_{a}_{b}_{c}_{d}_ad.nconf"))
            output(G_bc, os.path.join(outdir, f"{confname}_contractible_00_{a}_{b}_{c}_{d}_bc.nconf"))
        if oneedge_noncontractible:
            print(f"noncontractible, 00-onedge, a, b, c, d: {a, b, c, d} in {confname}")
            G_ab = gen_annular_island(n, r, G, a, b)
            G_cd = gen_annular_island(n, r, G, c, d)
            output(G_ab, os.path.join(outdir, f"{confname}_noncontractible_00_{a}_{b}_{c}_{d}_ab.nconf"))
            output(G_cd, os.path.join(outdir, f"{confname}_noncontractible_00_{a}_{b}_{c}_{d}_cd.nconf"))


def dist01(n, r, G, dist, contract_dist, confname, outdir):
    ab0_cd1s = find_ab_cd(0, 1, n, r, contract_dist)
    for a, b, c, d in ab0_cd1s:
        abpaths = allPaths(n, G, a, b)
        bcpaths = allPaths(n, G, b, c)
        cdpaths = allPaths(n, G, c, d)
        dapaths = allPaths(n, G, d, a)
        equivalent_contractible = True
        equivalent_noncontractible = True
        for abpath in abpaths:
            for cdpath in cdpaths:
                component1 = getComponent1(n, r, G, abpath, cdpath)
                component2 = getComponent2(n, r, G, abpath, cdpath)
                s1, t1 = sizeOfVertices(r, component1)
                s2, t2 = sizeOfVertices(r, component2)
                size1 = (s1 + 1) // 2 + t1
                size2 = (s2 + 1) // 2 + t2
                l1 = len(abpath) - 1
                l2 = len(cdpath) - 1
                # contractible cycle
                if (l1 + l2 <= 4 and min(size1, size2) > 0) or (l1 + l2 == 5 and min(size1, size2) > 1):
                    equivalent_contractible = False
                # annulus cut
                if (l1 + l2 <= 4 and min(size1, size2) > 0) or (l1 + l2 == 5 and l1 >= 2 and l2 >= 2 and min(size1, size2) > 1):
                    equivalent_noncontractible = False
        for bcpath in bcpaths:
            for dapath in dapaths:
                component1 = getComponent1(n, r, G, bcpath, dapath)
                component2 = getComponent2(n, r, G, bcpath, dapath)
                s1, t1 = sizeOfVertices(r, component1)
                s2, t2 = sizeOfVertices(r, component2)
                size1 = (s1 + 1) // 2 + t1
                size2 = (s2 + 1) // 2 + t2
                l1 = len(bcpath) - 1
                l2 = len(dapath) - 1
                # annulus cut
                if (l1 + l2 <= 4 and min(size1, size2) > 0) or (l1 + l2 == 5 and l1 >= 2 and l2 >= 2 and min(size1, size2) > 1):
                    equivalent_contractible = False
                # contractible cycle
                if (l1 + l2 <= 4 and min(size1, size2) > 0) or (l1 + l2 == 5 and min(size1, size2) > 1):
                    equivalent_noncontractible = False
        if equivalent_contractible:
            print(f"contractible, 01-equivalent, a, b, c, d: {a, b, c, d} in {confname}")
            G_ad = gen_annular_island(n, r, G, a, d)
            G_bc = gen_annular_island(n, r, G, b, c)
            output(G_ad, os.path.join(outdir, f"{confname}_contractible_01_{a}_{b}_{c}_{d}_ad.nconf"))
            output(G_bc, os.path.join(outdir, f"{confname}_contractible_01_{a}_{b}_{c}_{d}_bc.nconf"))
        if equivalent_noncontractible:
            print(f"noncontractible, 01-equivalent, a, b, c, d: {a, b, c, d} in {confname}")
            G_ab = gen_annular_island(n, r, G, a, b)
            G_cd = gen_annular_island(n, r, G, c, d)
            output(G_ab, os.path.join(outdir, f"{confname}_noncontractible_01_{a}_{b}_{c}_{d}_ab.nconf"))
            output(G_cd, os.path.join(outdir, f"{confname}_noncontractible_01_{a}_{b}_{c}_{d}_cd.nconf"))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('file', help='The configuration file')
    parser.add_argument("-o", "--outdir", help='The directory that annular island files are placed')
    parser.add_argument("-e", "--edges", nargs="+")
    args = parser.parse_args()

    path = args.file
    confname = os.path.splitext(os.path.basename(path))[0]
    outdir = args.outdir
    edges = args.edges

    n, r, G, degree = ReadPrimalFromFile(path)
    edgeIndexes = LabelEdges(n, r, G)

    dist = WF(n, r, G, [], edgeIndexes)
    contract_dist = WF(n, r, G, edges, edgeIndexes)

    dist00(n, r, G, dist, contract_dist, confname, outdir)
    dist01(n, r, G, dist, contract_dist, confname, outdir)


if __name__ == "__main__":
    main()



