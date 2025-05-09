import glob
import heapq
import argparse
import os
from collections import deque


# configuration のファイルを読む。
# n: 頂点数
# r: リングサイズ
# G: 隣接リスト
# degrees: 次数 (ringの頂点の次数は便宜的に0にしている。)
def readConf(path: str):
    with open(path, "r") as f:
        f.readline()
        n, r = map(int, f.readline().split())
        G = [[] for _ in range(n)]
        for i in range(r):
            G[i].append((i + 1) % r)
            G[(i + 1) % r].append(i)
        degrees = [0 for _ in range(n)]
        for i in range(n-r):
            v, d, *us = map(int, f.readline().split())
            v -= 1
            assert v == i + r
            degrees[v] = d
            for u in us:
                u -= 1
                G[v].append(u)
                if u < r:
                    G[u].append(v)
        return n, r, G, degrees


# n: free completion with ring の頂点サイズ
# r: リングサイズ
# G: free completion with ring の隣接リスト
#
# ring の辺と ring の点と configuration の点を結ぶ辺を取り除いたグラフの隣接リストを返す。
def removeRing(n: int, r: int, G: list):
    removedG = [[] for _ in range(len(G))]
    for i in range(r):
        removedG[i] = []
    for i in range(r, n):
        removedG[i] = list(filter(lambda x: x >= r, G[i]))
    return removedG


# G がカット点を持つか
def hasCutVertex(n: int, r: int, G: list):
    num = [-1 for _ in range(n)]
    low = [-1 for _ in range(n)]
    def dfs(v: int, par: int, order: int):
        has_cutvertex = False
        num[v] = order
        order += 1
        low[v] = num[v]
        n_child = 0
        for u in G[v]:
            if u == par:
                continue
            if u < r:
                continue
            if num[u] != -1:
                low[v] = min(low[v], num[u])
                continue
            n_child += 1
            order, b = dfs(u, v, order)
            has_cutvertex = has_cutvertex or b
            low[v] = min(low[v], low[u])
            if par != -1 and num[v] <= low[u]:
                has_cutvertex = True
        if par == -1 and n_child >= 2:
            has_cutvertex = True
        return order, has_cutvertex
    _, res = dfs(r, -1, 0)
    return res


# グラフ G 上で s から t の最短経路を列挙する。 
def shortestPaths(n: int, G: list, s: int, t: int):
    dist = [300 for _ in range(n)]
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
        assert len(path) == dist[t] + 1
        if path in unique_paths:
            continue
        unique_paths.append(path)
    
    return unique_paths


# Warshall-Floyd
# All-pairs shorest path
def WF(n: int, G: list):
    dist = [[300 for _ in range(n)] for _ in range(n)]
    for i in range(n):
        dist[i][i] = 0
    for v in range(n):
        for u in G[v]:
            dist[u][v] = 1
            dist[v][u] = 1
    for k in range(n):
        for i in range(n):
            for j in range(n):
                dist[i][j] = min(dist[i][k] + dist[k][j], dist[i][j])
    return dist


# n: free completion with ring の頂点サイズ
# r: リングサイズ
# dist: configuration の辺のみを使った free completion with its ring 上の距離, 
#       つまり, n x n サイズの行列で dist[i][j] := i から j までの距離。
#
# configuration の 2 頂点であって、距離が 5 であるペアの集合を返す。
def getPairsDist5(n: int, r: int, dist: list):
    pairs = []
    for i in range(r, n):
        for j in range(i + 1, n):
            assert dist[i][j] <= 5
            if dist[i][j] == 5:
                pairs.append((i, j))
    return pairs


# n: free completion with ring の頂点サイズ
# G: free completion with ring の隣接リスト
#
# diaognal[(u, v)] := {w : uvw が G 上で triangle になっている。} を計算する。
# configuration の場合は len(diagonal[e]) <= 2 を満たす。
def calcDiagonalVertices(n: int, G: list):
    diagonal = dict()

    for u in range(n):
        for v in G[u]:
            diagonal[(u, v)] = []

    for e in diagonal.keys():
        for u in G[e[0]]:
            for v in G[e[1]]:
                if u == v:
                    diagonal[e].append(u)
        assert len(diagonal[e]) <= 2
    
    return diagonal


# n: free completion with ring の頂点サイズ
# r: リングサイズ
# G: free completion with ring の隣接リスト
# dist: configuration の距離
# cut: G の頂点集合
#
# 頂点集合 cut によって分けられる 2 (or 1) つの連結成分の頂点数を計算する。
# 
def sizeDividedByCut(n: int, r: int, G: list, dist: list, cut: list):
    # 連結成分の計算
    component_id = [-1 for _ in range(n)]
    def dfs(v: int, c: int):
        component_id[v] = c
        for u in G[v]:
            if u in cut:
                continue
            if component_id[u] != -1:
                continue
            dfs(u, c)
        return
    num_component = 0
    for v in range(n):
        if v not in cut and component_id[v] == -1:
            dfs(v, num_component)
            num_component += 1
    assert num_component == 1 or num_component == 2

    # 連結成分の頂点数の計算。
    size_component = [0 for _ in range(num_component)]
    size_component_ring = [0 for _ in range(num_component)]
    vertices_dist5 = [set() for _ in range(num_component)]
    for v in range(n):
        if v >= r and component_id[v] != -1:
            size_component[component_id[v]] += 1
            for u in range(n):
                if dist[u][v] == 5:
                    vertices_dist5[component_id[v]].add(u)

    for v in range(n):
        if v >= r:
            incident = [0 for _ in range(num_component)]
            for u in G[v]:
                if u < r and component_id[u] != -1:
                    incident[component_id[u]] += 1
            for i in range(num_component):
                if v not in vertices_dist5[i]:
                    size_component_ring[i] = max(size_component_ring[i], incident[i])


    if num_component == 1:
        return size_component[0] + size_component_ring[0], 0
    elif num_component == 2:
        return size_component[0] + size_component_ring[0], size_component[1] + size_component_ring[1]
    else:
        assert False


def isForbiddenCut(cutsize: int, component1_size: int, component2_size: int):
    if cutsize <= 4:
        return min(component1_size, component2_size) > 0
    elif cutsize == 5:
        return min(component1_size, component2_size) > 1
    elif cutsize == 6:
        return min(component1_size, component2_size) > 3
    else:
        return False


# n: free completion with ring の頂点サイズ
# r: リングサイズ
# G: free completion with ring の隣接リスト
# u: configuration の頂点
# 
# u に隣接している ring の頂点を ring に並んでいる順 (e.g. 0,1,2 r-1,0,1 など) に返す。
def verticesOfRingAdjacent(n: int, r: int, G: list, u: int):
    vertices = list(filter(lambda x: x < r, G[u]))
    vertices.sort()
    for i in range(1, len(vertices)):
        if vertices[i] - vertices[i - 1] != 1:
            vertices = vertices[i:] + vertices[:i]
            break
    for i in range(1, len(vertices)):
        assert vertices[i] - vertices[i - 1] == 1 or (vertices[i - 1] == r - 1 and vertices[i] == 0), \
            f"vertices are not place in order of ring.\n G: {G}\n u: {u}"
    return vertices


# r: リングサイズ
# diagonal: diagonal_vertex 
# v: configuration の頂点
# v_neighbor_index: v_neighbors の index
# v_neighbors: v に隣接している ring の点 (ring で並んでいる順に並んでいる。)
#
# 辺 v v_neighbors[v_neighbor_index] の diagonal vertices を適切に並び替えた頂点の配列を返す。
def getRotationalDiagonal(r: int, diagonal: dict, v: int, v_neighbor_index: int, v_neighbors: list):
    neighbor_v = v_neighbors[v_neighbor_index]
    vs = diagonal[(v, neighbor_v)]
    assert len(vs) == 2

    if len(v_neighbors) == 1:
        prev = neighbor_v - 1 if neighbor_v > 0 else r - 1
        diagPrev = diagonal[(neighbor_v, prev)]
        assert len(diagPrev) == 1
        if vs[1] == diagPrev[0]:
            vs[0], vs[1] = vs[1], vs[0]
    else:
        if v_neighbor_index < len(v_neighbors) - 1:
            if vs[0] == v_neighbors[v_neighbor_index + 1]:
                vs[0], vs[1] = vs[1], vs[0]
            assert vs[1] == v_neighbors[v_neighbor_index + 1]
        else:
            if vs[1] == v_neighbors[v_neighbor_index - 1]:
                vs[0], vs[1] = vs[1], vs[0]
            assert vs[0] == v_neighbors[v_neighbor_index - 1]
            
    return vs


# (u, neighvor_v), (neighbor_u, v), (xu, xv), (yu, yv) を対応させたときに対応する頂点のうち
# 頂点 x(= xu, xv), y(= yu, yv) の近傍にある頂点を計算する。
def getCorrespondingVertices(n: int, r: int, G: list, diagonal: dict, u: int, v: int,
    neighbor_u: int, neighbor_v: int, xu: int, yu: int, xv: int, yv: int):
    # corresponding_vertices[i] と i が対応している。
    corresponding_vertices = [-1 for _ in range(n)]
    # これまでの対応関係
    corresponding_vertices[u] = neighbor_v
    corresponding_vertices[neighbor_v] = u
    corresponding_vertices[v] = neighbor_u
    corresponding_vertices[neighbor_u] = v
    corresponding_vertices[xu] = xv
    corresponding_vertices[xv] = xu
    corresponding_vertices[yu] = yv
    corresponding_vertices[yv] = yu

    alreadyCorrespond = lambda x: corresponding_vertices[x] != -1
    
    # corresponding_edges_u[i], corresponding_edges_v[i] が対応している。
    corresponding_edges_u = [(u, xu), (u, yu), (neighbor_u, xu), (neighbor_u, yu)]
    corresponding_edges_v = [(neighbor_v, xv), (neighbor_v, yv), (v, xv), (v, yv)]
    for eu, ev in zip(corresponding_edges_u, corresponding_edges_v):
        edge_u = eu
        edge_v = ev
        while len(diagonal[edge_u]) >= 2 and len(diagonal[edge_v]) >= 2:
            if (alreadyCorrespond(diagonal[edge_u][0]) and alreadyCorrespond(diagonal[edge_u][1])) or \
               (alreadyCorrespond(diagonal[edge_v][0]) and alreadyCorrespond(diagonal[edge_v][1])):
                break
            assert alreadyCorrespond(diagonal[edge_u][0]) or alreadyCorrespond(diagonal[edge_u][1])
            assert alreadyCorrespond(diagonal[edge_v][0]) or alreadyCorrespond(diagonal[edge_v][1])
            vertex_u = diagonal[edge_u][1] if alreadyCorrespond(diagonal[edge_u][0]) else diagonal[edge_u][0]
            vertex_v = diagonal[edge_v][1] if alreadyCorrespond(diagonal[edge_v][0]) else diagonal[edge_v][0]
            corresponding_vertices[vertex_u] = vertex_v
            corresponding_vertices[vertex_v] = vertex_u
            edge_u = (vertex_u, eu[1])
            edge_v = (vertex_v, ev[1])

    for i in range(n):
        if corresponding_vertices[i] != -1:
            assert corresponding_vertices[corresponding_vertices[i]] == i, f"getCorrespondingVertices may have some bug."
    
    return corresponding_vertices

# conf 上の 2 点が同一視されているかどうかをチェックする。
def checkNonValidCorrespondingVertices(n: int, r: int, corresponding_vertices: list):
    for i in range(r, n):
        if corresponding_vertices[i] != -1 and corresponding_vertices[i] >= r:
            return False # non valid
    return True # valid


def checkContractible(n: int, r: int, G: list, removedG: list, diagonal: dict, u: int, v: int, 
    neighbor_u: int, neighbor_v: int, xu: int, yu: int, xv: int, yv: int):
    corresponding_vertices = getCorrespondingVertices(n, r, G, diagonal, u, v, 
        neighbor_u, neighbor_v, xu, yu, xv, yv)
    if not checkNonValidCorrespondingVertices(n, r, corresponding_vertices):
        return False
    
    dist = WF(n, removedG)
    
    # 1
    paths = shortestPaths(n, removedG, u, v)
    assert len(paths[0]) == 6
    for path in paths:
        s0, s1 = sizeDividedByCut(n, r, G, dist, path + [neighbor_u, neighbor_v])
        if isForbiddenCut(6, s0, s1):
            return False
    
    # 2
    for vertex_u, vertex_v in zip([xu, yu], [xv, yv]):
        if vertex_u < r and vertex_v < r:
            # vertex_u, vertex_v もリングの頂点
            # configuration の異なる 2 頂点は同一視されないから、
            # vertex_u に隣接している configuration の頂点 neighbor_vertex_u と
            # vertex_v に隣接している configuration の頂点 neighbor_vertex_v を結ぶパスと vertex_u, vertex_v で
            # 分けられる 2 つの頂点集合を考える。
            vertex_u_neighbors = list(filter(lambda w: w >= r, G[vertex_u]))
            vertex_v_neighbors = list(filter(lambda w: w >= r, G[vertex_v]))
            for neighbor_vertex_u in vertex_u_neighbors:
                for neighbor_vertex_v in vertex_v_neighbors:
                    paths = shortestPaths(n, removedG, neighbor_vertex_u, neighbor_vertex_v)
                    # パスと頂点サイズの処理, vertex_u, vertex_v
                    for path in paths:
                        s0, s1 = sizeDividedByCut(n, r, G, dist, path + [vertex_u, vertex_v])
                        if isForbiddenCut(len(path) + 1, s0, s1):
                            return False
        elif vertex_u < r and vertex_v >= r:
            # vertex_u がリングの頂点、 vertex_v が configuration の頂点
            vertex_u_neighbors = list(filter(lambda w: w >= r, G[vertex_u]))
            for neighbor_vertex_u in vertex_u_neighbors:
                neighbor_vertex_v = corresponding_vertices[neighbor_vertex_u]
                if neighbor_vertex_v == -1:
                    continue
                assert neighbor_vertex_v < r and neighbor_vertex_v in G[vertex_v]
                paths = shortestPaths(n, removedG, neighbor_vertex_u, vertex_v)
                # パスと頂点サイズの処理, vertex_u, neighbor_vertex_v
                for path in paths:
                    s0, s1 = sizeDividedByCut(n, r, G, dist, path + [vertex_u, neighbor_vertex_v])
                    if isForbiddenCut(len(path), s0, s1):
                        return False
        elif vertex_u >= r and vertex_v < r:
            # vertex_u が configuration の頂点、 vertex_v がリングの頂点
            vertex_v_neighbors = list(filter(lambda w: w >= r, G[vertex_v]))
            for neighbor_vertex_v in vertex_v_neighbors:
                neighbor_vertex_u = corresponding_vertices[neighbor_vertex_v]
                if neighbor_vertex_u == -1:
                    continue
                assert neighbor_vertex_u < r and neighbor_vertex_u in G[vertex_u]
                paths = shortestPaths(n, removedG, vertex_u, neighbor_vertex_v)
                # パスと頂点サイズの処理, neighbor_vertex_u, vertex_v
                for path in paths:
                    s0, s1 = sizeDividedByCut(n, r, G, dist, path + [neighbor_vertex_u, vertex_v])
                    if isForbiddenCut(len(path), s0, s1):
                        return False
        else:
            assert False, "identification of two vertices in a configuration is not valid"
    
    return True


# n: free completion with ring の頂点サイズ
# r: リングサイズ
# G: free completion with ring の隣接リスト
# removedG: configuration の隣接リスト
#
# u, v: G 上で距離 5 の頂点対
# 
def checkDist5(n: int, r: int, G: list, removedG: list, u: int, v: int):
    u_neighbors = verticesOfRingAdjacent(n, r, G, u)
    v_neighbors = verticesOfRingAdjacent(n, r, G, v)
    diagonal = calcDiagonalVertices(n, G)

    uv_possible_cnt = 0 # uv_is_possible <-> an edge uv can exist

    for i in range(len(u_neighbors)):
        for j in range(len(v_neighbors)):
            diagonal_u = getRotationalDiagonal(r, diagonal, u, i, u_neighbors)
            diagonal_v = getRotationalDiagonal(r, diagonal, v, j, v_neighbors)

            # contractible
            if checkContractible(n, r, G, removedG, diagonal, u, v, u_neighbors[i], v_neighbors[j], 
                diagonal_u[0], diagonal_u[1], diagonal_v[1], diagonal_v[0]):
                print(f"contractible dangerous pair: {u} = {v_neighbors[j]}, {u_neighbors[i]} = {v}, {diagonal_u[0]} = {diagonal_v[1]}, {diagonal_u[1]} = {diagonal_v[0]}")
                uv_possible_cnt += 1

    return uv_possible_cnt


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('dir', help='The directory that includes configuration files')
    args = parser.parse_args()

    all_cnt = 0
    for path in sorted(glob.glob(os.path.join(args.dir, "*.conf"))):
        n, r, G, _ = readConf(path)
        removedG = removeRing(n, r, G)
        dist = WF(n, removedG)
        pairs = getPairsDist5(n, r, dist)
        danger = False
        for u, v in pairs:
            uv_cnt = checkDist5(n, r, G, removedG, u, v)
            all_cnt += uv_cnt
            danger = danger or (uv_cnt > 0)
        if danger:
            print(f"dangerous pair exists in {path}")
    print(f"the number of dangerous pair is {all_cnt}.")
    

if __name__ == "__main__":
    main()