import json, re
from pathlib import Path
tmp = Path(r"E:\github\py\_uf_check")
axioms = [r["axiom"] for r in json.loads(tmp.joinpath("axioms.json").read_text(encoding="utf-8"))]
modules = [r["module"].replace("'", "") for r in json.loads(tmp.joinpath("lean.json").read_text(encoding="utf-8"))]
hierarchy = json.loads(tmp.joinpath("hierarchy.json").read_text(encoding="utf-8"))

def norm_path(name):
    name = re.sub(r"\.given(?=\.|$)", ".of", name)
    name = re.sub(r"\.Is(?=\.|$)", ".is", name)
    name = re.sub(r"\.In(?=\.|$)", ".in", name)
    return name

def strip(name):
    return re.sub(r"\.[a-z_0-9]+$", "", name)

formalized = set()
for m in modules:
    m = norm_path(m)
    formalized.add(m)
    formalized.add(strip(m))

unformalized = []
for a in axioms:
    norm = norm_path(a)
    ok = norm in formalized or strip(norm) in formalized
    if not ok:
        unformalized.append(a)

print(f"total py axioms: {len(axioms)}")
print(f"lean modules: {len(modules)}")
print(f"unformalized: {len(unformalized)}")
print("--- unformalized list ---")
for a in sorted(unformalized):
    print(a)

deps = {}
dependents = {}
nodes = set()
for row in hierarchy:
    caller, callee = row["caller"], row["callee"]
    deps.setdefault(caller, set()).add(callee)
    dependents.setdefault(callee, set()).add(caller)
    nodes.add(caller)
    nodes.add(callee)
uf_set = set(unformalized)
for a in uf_set:
    nodes.add(a)

tdep = {}
def count_dependents(n, stack):
    if n in tdep:
        return tdep[n]
    if n in stack:
        return set()
    stack.add(n)
    s = set()
    for c in dependents.get(n, ()):
        s.add(c)
        s |= count_dependents(c, stack)
    stack.discard(n)
    tdep[n] = s
    return s

indeg = {n: len(deps.get(n, ())) for n in nodes}
heap = sorted([n for n in nodes if indeg[n] == 0], key=lambda n: -len(count_dependents(n, set())))
order = []
while heap:
    n = heap.pop(0)
    order.append(n)
    for c in dependents.get(n, ()):
        indeg[c] -= 1
        if indeg[c] == 0:
            heap.append(c)
            heap.sort(key=lambda x: -len(count_dependents(x, set())))
wanted = [a for a in order if a in uf_set][:10]
print("--- most wanted 10 ---")
for a in wanted:
    print(f"{norm_path(a)}  depth={len(count_dependents(a, set()))}")
