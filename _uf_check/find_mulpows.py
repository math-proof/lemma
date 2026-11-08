import os
root = r"E:\github\py\Lemma"
needles = ("DetBlock_Stack_MulPowS", "Mul_Prod_Factorial.vandermonde")
hits = 0
for dp, dns, fns in os.walk(root):
    dns[:] = [d for d in dns if d != "__pycache__"]
    for f in fns:
        if not f.endswith(".py"):
            continue
        p = os.path.join(dp, f)
        with open(p, encoding="utf-8", errors="ignore") as fh:
            for i, l in enumerate(fh, 1):
                if any(n in l for n in needles):
                    print(f"{p}:{i}:{l.rstrip()}")
                    hits += 1
print(f"DONE hits={hits}")
