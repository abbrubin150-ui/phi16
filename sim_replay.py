import json
from collections import defaultdict, deque
from math import log2

with open("examples/events.json", "r") as f:
    data = json.load(f)

with open("spec/ssot/phi16.instance.json", "r") as f:
    cfg = json.load(f)

E = data["events"]
id2e = {e["id"]: e for e in E}

# Build graph of justifications
V = set(id2e.keys())
E_edges = set()
for e in E:
    for j in e.get("justifies", []):
        if j in V:
            E_edges.add((e["id"], j))

def dia_graph():
    return len(E_edges) / max(len(V), 1)

def topo_order():
    indeg = defaultdict(int)
    adj = defaultdict(list)
    for u, v in E_edges:
        indeg[v] += 1
        adj[u].append(v)
    q = deque([v for v in V if indeg[v] == 0])
    order = []
    while q:
        u = q.popleft()
        order.append(u)
        for w in adj[u]:
            indeg[w] -= 1
            if indeg[w] == 0:
                q.append(w)
    return order if len(order) == len(V) else None

def replay_ok():
    return topo_order() is not None

def dia_replay():
    return 1.0 if replay_ok() else 0.0

def entropy(p):
    return -sum(pi * log2(pi) for pi in p if pi > 0)

def dia_info():
    types = [e.get("type", "X") for e in E]
    from collections import Counter
    c = Counter(types)
    total = sum(c.values())
    p = [v / total for v in c.values()]
    H = entropy(p) if total > 0 else 0.0
    recovered = min(H, len(E_edges) / max(len(V), 1))
    return 0.0 if H == 0 else recovered / H

# Parameters from SSOT instance
weights = cfg["weights"]
tau = cfg["tau"]

# Metrics
G = dia_graph()
R = dia_replay()
I = dia_info()
D = weights["w_g"] * G + weights["w_i"] * I + weights["w_r"] * R

print("DIA_graph =", round(G, 4))
print("DIA_replay =", round(R, 4))
print("DIA_info  =", round(I, 4))
print("DIA       =", round(D, 4))

mode = "RUN"
if not replay_ok():
    mode = "HOLD"
else:
    prev = 1.0  # assume maximum previous DIA
    if D < prev - tau:
        mode = "SAFE"

print("mode =", mode)
