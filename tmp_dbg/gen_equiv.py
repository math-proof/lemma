import io, re

SRC = "/home/cosmos/src/lean/sympy/combinatorics/permutations/Basics.lean"
OUT = "/home/cosmos/src/lean/Lemma/Equiv/Basics.lean"
URL = "https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Permutations/Basics.lean"
NS = "AlgebraicCombinatorics"
QUAL = ["Sn", "bracketN", "transposition", "simpleTransposition", "cyc", "IsInvolution", "IsCycle",
        "cycleSupport", "twoLineNotation", "oneLineNotation", "oneLineNotationToPerm", "cycleDigraph",
        "symmetricGroup_conj_iso", "Permutation", "SymmetricGroup",
        "oneLineNotation_length", "oneLineNotation_nodup"]
SKIP_PARSE = {"simpleTransposition_braid", "simpleTransposition_eq_swap_explicit"}
NAME_OVERRIDE = {"perm_pow_succ'": "perm_pow_succ'_eq"}
BINDER_RENAME = {"_hlen'": "hlen'", "_h": "h"}
TYPE_RE = re.compile(r"^([A-Z][A-Za-z0-9_]*(?:\s+[A-Z][A-Za-z0-9_]*)*)\s*:\s*(Type\*|Type _)$")


def qualify(t):
    t = re.sub(r"s\[([A-Za-z_][A-Za-z0-9_']*)\]", r"(simpleTransposition \1)", t)
    for name in sorted(QUAL, key=len, reverse=True):
        t = re.sub(r"(?<![\w.])" + re.escape(name) + r"\b", NS + "." + name, t)
    return t


def snake(name):
    s = re.sub(r"(?<!^)(?<![A-Z0-9])([A-Z])", r"_\1", name)
    return s.replace(".", "_").lower()


def close_of(c):
    return {'(': ')', '{': '}', '[': ']'}[c]


def parse_groups(text, i):
    groups = []
    n = len(text)
    while i < n:
        while i < n and text[i] in " \t\n":
            i += 1
        if i >= n or text[i] not in "([{":
            break
        opener = text[i]
        closer = close_of(opener)
        depth = 0
        j = i
        while j < n:
            if text[j] == opener:
                depth += 1
            elif text[j] == closer:
                depth -= 1
                if depth == 0:
                    break
            j += 1
        groups.append((opener, text[i + 1:j], closer))
        i = j + 1
    return groups, i


def split_binder_group(body):
    depth = 0
    k = 0
    n = len(body)
    while k < n:
        c = body[k]
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        elif c == ":" and depth == 0:
            break
        k += 1
    if k >= n:
        return None
    return body[:k].strip(), body[k + 1:].strip()


def find_conclusion_end(text, start):
    depth = 0
    k = start
    n = len(text)
    while k < n - 1:
        c = text[k]
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        elif depth == 0 and c == ":" and text[k + 1] == "=":
            return k
        k += 1
    return -1


def concl_shape(concl_flat):
    depth = 0
    has_le = has_lt = has_iff = False
    for c in concl_flat:
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        elif depth == 0:
            if c == "\u2194":
                has_iff = True
            elif c == "\u2264":
                has_le = True
            elif c == "<":
                has_lt = True
    if has_iff:
        return "iff"
    if has_le:
        return "le"
    if has_lt:
        return "lt"
    if re.search(r"\bIs[A-Z]", concl_flat) or re.search(r"\.(Is[A-Z]|Nodup)\b", concl_flat):
        return "is"
    return "eq"


SUFFIX = {"iff": "_iff", "le": "_le", "lt": "_lt", "is": "_is", "eq": "_eq"}


def wrap_name(srcname, concl_flat):
    s = snake(srcname)
    suf = SUFFIX[concl_shape(concl_flat)]
    if any(s.endswith("_" + x) for x in ("eq", "iff", "le", "lt", "is")):
        return s
    return s + suf


def reindent_concl(concl_text):
    concl = qualify(concl_text)
    out = []
    base = None
    for l in concl.split("\n"):
        if l.strip() == "":
            continue
        ind = len(l) - len(l.lstrip())
        if base is None:
            base = ind
            out.append("  " + l.strip())
        else:
            out.append(" " * (ind - base + 2) + l.strip())
    return out


lines = io.open(SRC, encoding="utf-8").read().split("\n")
n = len(lines)
thms = []
i = 0
while i < n:
    m = re.match(r'^theorem\s+([A-Za-z_][A-Za-z0-9_.\']*)', lines[i])
    if m:
        name = m.group(1)
        j = i
        raw = []
        end = -1
        while j < n:
            s = lines[j]
            if j > i and re.match(r'^(theorem|lemma|private|def|abbrev|instance|noncomputable|end|namespace|/--|/-!|@\[|open|variable|scoped|notation)', s):
                break
            raw.append(s)
            joined = "\n".join(raw)
            k = find_conclusion_end(joined, len(m.group(0)) if len(raw) == 1 else 0)
            if k >= 0 and (len(raw) > 1 or k >= len(m.group(0))):
                end = k
                break
            j += 1
        thms.append((name, "\n".join(raw), end))
        i = (j + 1) if end >= 0 else j
    else:
        i += 1

blocks = []
seen = set()
count = 0


def emit(wname, pre, cls, given, concl_lines, apply_target, args):
    global count
    assert wname not in seen, "duplicate " + wname
    seen.add(wname)
    count += 1
    b = ["/--", "[Basics](%s)" % URL, "-/", "@[path]"]
    allb = ["  " + x for x in (pre + cls + given)]
    if not allb:
        b.append("private lemma %s :" % wname)
    else:
        b.append("private lemma %s" % wname)
        for idx, bl in enumerate(allb):
            b.append(bl + (" :" if idx == len(allb) - 1 else ""))
    b.append("-- imply")
    b.extend(concl_lines)
    b[-1] = b[-1] + " := by"
    b.append("-- proof")
    b.append("  apply %s%s" % (apply_target, (" " + " ".join(args)) if args else ""))
    blocks.append("\n".join(b))


for name, raw, end in thms:
    if name in SKIP_PARSE:
        continue
    assert end >= 0, "no := found for " + name
    header = raw[:end]
    after_name = header[len("theorem " + name):]
    groups, pos = parse_groups(after_name, 0)
    rest = after_name[pos:].lstrip()
    assert rest.startswith(":"), "no separator colon for " + name
    concl_text = rest[1:]

    cls = [opener + body + closer for opener, body, closer in groups if opener == "["]
    cls_idents = set()
    for ct in cls:
        cls_idents.update(re.findall(r"[A-Za-z_][A-Za-z0-9_]*", ct))
    pre_types = []
    given = []
    args = []
    for opener, body, closer in groups:
        gtext = opener + body + closer
        if opener == "[":
            continue
        sp = split_binder_group(body)
        if sp is not None:
            nm, tp = sp
            if TYPE_RE.match(nm + " : " + tp.strip()):
                names = nm.split()
                if any(x in cls_idents for x in names):
                    if opener == "(":
                        pre_types.append(gtext)
                else:
                    given.append("(" + nm + " : Type*)")
                    if opener == "(":
                        args.extend(BINDER_RENAME.get(t, t) for t in nm.split())
                continue
        if opener == "(" and sp is not None:
            args.extend(BINDER_RENAME.get(t, t) for t in sp[0].split())
        renamed = gtext
        if opener == "(" and sp is not None:
            for src, dst in BINDER_RENAME.items():
                renamed = renamed.replace("(" + src + " ", "(" + dst + " ")
        given.append(qualify(renamed))

    concl_lines = reindent_concl(concl_text)
    flat = " ".join(x.strip() for x in concl_lines)
    wname = NAME_OVERRIDE.get(name) or wrap_name(name, flat)
    if name == "symmetricGroup_conj_iso_self":
        given = ["(X : Type*)", "(f σ : Equiv.Perm X)"]
    emit(wname, pre_types, cls, given, concl_lines, NS + "." + name, args)

# hardcoded: simpleTransposition_braid (let-conclusion)
emit("simple_transposition_braid_eq", [], [], [
    "(i : Fin (n - 2))",
], [
    "  let i' : Fin (n - 1) := \u27e8i.val, by omega\u27e9",
    "  let i1 : Fin (n - 1) := \u27e8i.val + 1, by omega\u27e9",
    "  (AlgebraicCombinatorics.simpleTransposition i') * (AlgebraicCombinatorics.simpleTransposition i1) *",
    "    (AlgebraicCombinatorics.simpleTransposition i') =",
    "    (AlgebraicCombinatorics.simpleTransposition i1) * (AlgebraicCombinatorics.simpleTransposition i') *",
    "    (AlgebraicCombinatorics.simpleTransposition i1)",
], NS + ".simpleTransposition_braid", ["i"])

# hardcoded: simpleTransposition_eq_swap_explicit (let-conclusion)
emit("simple_transposition_eq_swap_explicit_eq", [], [], [
    "(k : Fin N)",
    "(hk : k.val + 1 < N)",
], [
    "  let i : Fin (N - 1) := \u27e8k.val, by omega\u27e9",
    "  AlgebraicCombinatorics.simpleTransposition i = Equiv.swap k \u27e8k.val + 1, hk\u27e9",
], NS + ".simpleTransposition_eq_swap_explicit", ["k", "hk"])

header = "import Mathlib\nimport sympy.Basic\nimport sympy.combinatorics.permutations.Basics\n\n\n"
body = "\n\n".join(blocks)
footer = "\n\n\n-- created on 2026-10-11\n"
io.open(OUT, "w", encoding="utf-8").write(header + body + footer)
print("wrote", OUT, "with", count, "wrappers")
