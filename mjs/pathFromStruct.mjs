/**
 * pathFromStruct.mjs
 * ==================
 * From Name.toJson `imply.struct`, enumerate ALL naming alternatives at each
 * AST node (cartesian product of child alts + local style choices), then the
 * caller exact-matches the existing lemma path against that set.
 *
 * Local style choices (examples):
 *   - method map with fun + receiver:
 *       FunMapRange   (Fun wraps Map+Receiver)
 *       Map_FunData   (Map named with function body)
 *   - operatorname/property with Fun child: also bare head (drop Fun detail)
 *   - eq: Left/eq/Right for every Left×Right pair
 */

export function lastNameSeg(name) {
  if (!name) return "";
  const s = String(name);
  const i = s.lastIndexOf(".");
  const seg = i >= 0 ? s.slice(i + 1) : s;
  if (!seg || seg === "[anonymous]" || seg === "anonymous" || seg === "_") return "";
  return seg;
}

export function camel(s) {
  if (!s) return "";
  return s.charAt(0).toUpperCase() + s.slice(1);
}

/** Lean decl name → lemma-path token (GetElem → Get by convention). */
const NAME_ALIAS = {
  GetElem: "Get",
  StdPart: "St",
  stdPart: "St",
  val: "Val",
  Val: "Val",
  coe: "Val",
  HMul: "Mul",
  HAdd: "Add",
  HSub: "Sub",
  HDiv: "Div",
  HPow: "Pow",
  HMod: "Mod",
  HAnd: "And",
  HOr: "Or",
  HXor: "Xor",
};

export function pathToken(seg) {
  if (!seg) return "";
  const c = camel(seg);
  return NAME_ALIAS[c] || c;
}

/** Count Lean explicit (`default`) binders on a forall type. */
export function explicitArity(type) {
  if (!type || type.kind !== "forall") return 0;
  const binders = type.binders || [];
  return binders.filter((b) => !b.binder || b.binder === "default").length;
}

/** Anonymous fn by explicit arity: 1 → UFn, 2 → BFn. */
export function fnArityTag(type) {
  const n = explicitArity(type);
  if (n === 1) return "UFn";
  if (n === 2) return "BFn";
  return "";
}

/** Tensor.mk / Inductive.mk → type name (Mk alone is uninformative). */
export function ctorTypeName(name) {
  const s = String(name || "");
  const segs = s.split(".").filter(Boolean);
  if (segs.length >= 2 && segs[segs.length - 1] === "mk") {
    return pathToken(segs[segs.length - 2]);
  }
  return pathToken(lastNameSeg(s));
}

function uniq(xs) {
  return [...new Set((xs || []).filter(Boolean))];
}

/** Cartesian join of alt lists via joiner(L, R). Empty side acts as identity. */
function cartJoin(leftAlts, rightAlts, joiner) {
  const L = leftAlts?.length ? leftAlts : [""];
  const R = rightAlts?.length ? rightAlts : [""];
  const out = [];
  for (const l of L) {
    for (const r of R) {
      if (l && r) out.push(joiner(l, r));
      else out.push(l || r);
    }
  }
  return uniq(out);
}

function joinHeadChild(head, child) {
  if (!child) return head;
  if (!head) return child;
  // BFn/UFn arity tags always Camel-compose (BFnUFnFunIte, not BFnUFn_FunIte)
  if (/^(BFn|UFn)+$/.test(head)) {
    return head + child;
  }
  // Fun… child → Snake; otherwise Camel compose
  if (child.startsWith("Fun") || child.includes("_")) {
    // Map_FunData already has underscore — Camel-prefix: Flatten + Map_FunData → FlattenMap_FunData
    if (!child.startsWith("Fun") && child.includes("_")) return head + child;
    return head + "_" + child;
  }
  return head + child;
}

/** Camel Fun compose (MapFunPow) — also emitted alongside Snake Map_FunPow. */
function joinHeadChildCamelFun(head, child) {
  if (!child) return head;
  if (!head) return child;
  return head + child;
}

/**
 * Identical direct children under an op: put S after the first Camel atom.
 * Map+Map → MapS; MapRange+MapRange → MapSRange (not MapRangeS).
 */

/** ArchimedeanClass.mk x — used only for Infinite / Infinitesimal (see sympy/series/limits.lean). */
function isArchimedeanMk(node) {
  if (!node || typeof node !== "object") return false;
  const raw = String(node.name || node.op || "");
  return /ArchimedeanClass\.mk$/i.test(raw) || raw === "ArchimedeanClass.mk";
}

function isZeroConst(node) {
  if (!node || node.kind !== "const") return false;
  const v = node.value ?? node.nat ?? node.int;
  return v === 0 || v === "0";
}

function sameChildS(name) {
  if (!name) return "";
  // Prefer splitting on Camel atoms; keep leading underscore chunks intact
  if (name.includes("_")) {
    const i = name.indexOf("_");
    return name.slice(0, i) + "S" + name.slice(i);
  }
  const atoms = name.match(/[A-Z][a-z0-9]*|[A-Z]+(?![a-z])/g);
  if (!atoms || atoms.length <= 1) return name + "S";
  return atoms[0] + "S" + atoms.slice(1).join("");
}

/**
 * All name alternatives for this struct node (exact strings, no fuzzy).
 */
export function nameStructAlts(node, depth = 0) {
  if (!node || typeof node !== "object") return [];
  if (depth > 48) return [];
  const kind = node.kind;
  const go = (n) => nameStructAlts(n, depth + 1);

  if (kind === "symbol" || kind === "sort" || kind === "typeclass" || kind === "const") {
    // nat/int literals participate as path atoms (Gt_0, Get_0, …)
    if (kind === "const") {
      const v = node.value ?? node.nat ?? node.int;
      if (v === 0 || v === "0") return ["0"];
      // digits cannot appear bare in paths: 1 → One
      if (v === 1 || v === "1") return ["One"];
      if (v != null && String(v).length && String(v).length <= 8 && /^-?\d+$/.test(String(v))) {
        const n = String(v);
        if (n === "1") return ["One"];
        return [n]; // 0 and other small ints still allowed (Gt_0, …)
      }
      return [];
    }
    return [];
  }
  // proof terms / named lemmas in args are not path material
  if (kind === "lemma") return [];
  if (kind === "binder") return go(node.type);

  if (kind === "eq" || kind === "ne" || kind === "iff") {
    const left = go(node.args?.[0]);
    const right = go(node.args?.[1]);
    const mid = kind === "eq" ? "eq" : kind === "ne" ? "ne" : "is";
    const flat = { eq: "Eq", ne: "Ne", iff: "Is" }[kind];
    const out = [];
    // Both sides named → Left/eq/Right
    if (left.length && right.length) {
      out.push(...cartJoin(left, right, (L, R) => `${L}/${mid}/${R}`));
      // /as/ is an allowed spelling of equality in lemma paths
      if (kind === "eq") {
        out.push(...cartJoin(left, right, (L, R) => `${L}/as/${R}`));
      }
    } else {
      // Dropped side (bare symbol etc.): flat Eq_/Ne_/Is_<other>
      for (const R of right) out.push(flat + "_" + R);
      for (const L of left) out.push(flat + "_" + L);
    }
    return uniq(out.filter(Boolean));
  }

  if (kind === "lt" || kind === "gt" || kind === "le" || kind === "ge") {
    // ArchimedeanClass.mk x < 0  ⇒ Infinite;  0 < ArchimedeanClass.mk x  ⇒ Infinitesimal
    // (sympy/series/limits.lean: x ≃ ∞ / x ≃ 0)
    const a0 = node.args?.[0];
    const a1 = node.args?.[1];
    if (kind === "lt" || kind === "gt") {
      const leftArch = isArchimedeanMk(a0);
      const rightArch = isArchimedeanMk(a1);
      const left0 = isZeroConst(a0);
      const right0 = isZeroConst(a1);
      if (kind === "lt" && leftArch && right0) return ["Infinite"];
      if (kind === "lt" && left0 && rightArch) return ["Infinitesimal"];
      if (kind === "gt" && left0 && rightArch) return ["Infinite"]; // 0 > class ≡ class < 0
      if (kind === "gt" && leftArch && right0) return ["Infinitesimal"]; // class > 0 ≡ 0 < class
    }
    const tok = { lt: "Lt", gt: "Gt", le: "Le", ge: "Ge" }[kind];
    const kids = (node.args || []).map(go);
    const nonempty = kids.filter((k) => k.length);
    if (!nonempty.length) return [tok];
    // One side dropped: flat Lt_<other> (same rule as Eq_)
    if (nonempty.length === 1) {
      return uniq([
        ...nonempty[0].map((x) => tok + "_" + x),
        ...nonempty[0].map((x) => tok + x), // lossy Camel
      ]);
    }
    const out = [
      ...cartJoin(nonempty[0], nonempty[1], (a, b) => `${a}_${tok}_${b}`),
      // GtVal_0: Rel + Left + _ + Right
      ...cartJoin(nonempty[0], nonempty[1], (a, b) => `${tok}${a}_${b}`),
    ];
    return uniq(out);
  }

    if (kind === "and" || kind === "or") {
    const tok = kind === "and" ? "And" : "Or";
    const sideAlts = (node.args || []).map(go);
    const parts = sideAlts.filter((a) => a.length);
    if (!parts.length) return [tok];
    let out = parts.reduce(
      (acc, alts) => cartJoin(acc, alts, (a, b) => `${a}_${tok}_${b}`),
      [""],
    ).filter(Boolean);
    // And(P, Q) path conventions when one side is Not / unnamed Cond
    if (kind === "and" && sideAlts.length === 2) {
      const [L, R] = sideAlts;
      const leftNot = L.some((x) => x === "Not" || x.startsWith("Not"));
      const rightNot = R.some((x) => x === "Not" || x.startsWith("Not"));
      const leftEmpty = !L.length;
      const rightEmpty = !R.length;
      // unnamed proposition → Cond by default
      const leftCond = leftEmpty;
      const rightCond = rightEmpty;
      if (rightNot) {
        for (const l of L) {
          out.push(`${l}/Not`);
          out.push(tok + l); // AndBFnUFn (drop Not)
        }
      }
      if (leftNot) {
        for (const r of R) {
          out.push(`Not/${r}`);
          out.push(tok + r);
        }
      }
      if (rightCond && L.length) {
        for (const l of L) {
          out.push(`${l}/Cond`);
          out.push(tok + l); // AndBFnUFn (drop Cond)
        }
      }
      if (leftCond && R.length) {
        for (const r of R) {
          out.push(`Cond/${r}`);
          out.push(tok + r);
        }
      }
    }
    return uniq(out.filter(Boolean));
  }

if (kind === "forall") {
    const bodies = go(node.body);
    return bodies.length ? bodies.map((b) => "All_" + b) : ["All"];
  }
  if (kind === "exists") {
    const bodies = go(node.body);
    return bodies.length ? bodies.map((b) => "Any_" + b) : ["Any"];
  }
  if (kind === "fun") {
    const bodies = go(node.body);
    if (!bodies.length) return ["Fun"];
    return bodies.map((b) => (b.startsWith("Fun") ? b : "Fun" + b));
  }
  if (kind === "cons") return ["Cons"];

  if (kind === "operatorname" || kind === "function") {
    const rawName = String(node.name || node.op || "");
    // cast proof, value — omit proof; name value only
    if (/(^|\.)cast$/i.test(rawName)) {
      const args = (node.args || []).filter((a) => a && a.kind !== "lemma");
      const value = args.length ? args[args.length - 1] : null;
      const valAlts = value ? go(value) : [];
      return valAlts.length ? valAlts : [];
    }
    const head = ctorTypeName(node.name);
    if (!head) {
      const only = (node.args || []).map(go).filter((a) => a.length);
      return only.length ? only.reduce((acc, alts) => cartJoin(acc, alts, joinHeadChild), [""]).filter(Boolean) : [];
    }
    const argAlts = (node.args || []).map(go).filter((a) => a.length);
    if (!argAlts.length) return [head];
    let acc = [head];
    const all = [head];
    for (const alts of argAlts) {
      acc = cartJoin(acc, alts, joinHeadChild);
      all.push(...acc);
    }
    return uniq(all);
  }

  if (kind === "method" || kind === "property") {
    const head = pathToken(lastNameSeg(node.name));
    if (!head) {
      const only = (node.args || []).map(go).filter((a) => a.length);
      return only.length ? only.reduce((acc, alts) => cartJoin(acc, alts, joinHeadChild), [""]).filter(Boolean) : [];
    }
    const args = node.args || [];
    const idx = parseInt(node.idx ?? "-1", 10);

    // Split method self vs other args when idx is known
    let receiverAlts = [];
    const otherGroups = [];
    for (let i = 0; i < args.length; i++) {
      const alts = go(args[i]);
      if (!alts.length) continue;
      if (kind === "method" && i === idx) receiverAlts = alts;
      else otherGroups.push(alts);
    }
    const others = uniq(otherGroups.flat());
    const funOthers = others.filter((o) => o.startsWith("Fun"));

    // method(map): fun + receiver → TWO local styles
    if (kind === "method" && receiverAlts.length && funOthers.length) {
      const out = [];
      for (const r of receiverAlts) out.push("Fun" + head + r); // FunMapRange
      for (const f of funOthers) {
        out.push(head + "_" + f); // Map_FunGet
        out.push(head + f); // MapFunGet (Camel Fun)
      }
      // MapRange_FunGet: Camel Map+Range, then Snake Fun body
      for (const r of receiverAlts) {
        for (const f of funOthers) {
          out.push(joinHeadChild(head + r, f));
          out.push(joinHeadChild(joinHeadChild(head, r), f));
        }
      }
      // also lossy bare method
      out.push(head);
      return uniq(out);
    }

    // Compose head with every child alt group (property Flatten of Map_…)
    const groups = [];
    if (kind === "method" && receiverAlts.length) groups.push(receiverAlts);
    groups.push(...otherGroups);

    if (!groups.length) return [head];

    let acc = [head];
    const all = [head];
    for (const alts of groups) {
      acc = cartJoin(acc, alts, joinHeadChild);
      all.push(...acc); // keep prefixes (ResizeGet before ResizeGetSub)
    }
    return uniq(all);
  }

  // binary infix: a * b → Mul / A_Mul_B / Mul_B / A_Mul (lossy alts)
  if (kind === "infix" || kind === "infixl" || kind === "infixr") {
    const head = ctorTypeName(node.op || node.name || "");
    const left = go(node.args?.[0]);
    const right = go(node.args?.[1]);
    if (!head) {
      return cartJoin(left, right, (a, b) => (a && b ? a + b : a || b));
    }
    const out = [head];
    for (const L of left.length ? left : [""]) {
      for (const R of right.length ? right : [""]) {
        if (L && R) out.push(`${L}_${head}_${R}`);
        if (L && !R) out.push(L + head);
        if (!L && R) {
          out.push(head + R);
          out.push(head + "_" + R);
        }
        if (L && R) {
          out.push(L + head);
          out.push(head + R);
          out.push(head + "_" + R);
          out.push(L + "_" + head);
        }
      }
    }
    // also Camel compose when one side interesting (unary-ish)
    for (const L of left) out.push(joinHeadChild(head, L));
    for (const R of right) out.push(joinHeadChild(head, R));
    for (const L of left) {
      for (const R of right) {
        // Add + Map + Map → AddMapS; Pow + MapRange + MapRange → PowMapSRange
        if (L && R && L === R) out.push(head + sameChildS(L));
        else out.push(joinHeadChild(joinHeadChild(head, L), R));
      }
    }
    return uniq(out.filter(Boolean));
  }

  // special / prefix / etc.
  if (kind === "prefix" || kind === "postfix" || kind === "special") {
    const raw = node.op || node.name || kind;
    const head = ctorTypeName(raw);
    const args = (node.args || []).filter((a) => a && a.kind !== "lemma");
    // Fin.mk ⟨i, h⟩ — constructor noise; omit from paths (use child alts only if any)
    if (/Fin\.mk$/i.test(String(raw)) || (head === "Mk" && /Fin/i.test(String(raw)))) {
      const child = args.map(go).filter((a) => a.length);
      return child.length ? child.reduce((acc, alts) => cartJoin(acc, alts, joinHeadChild), [""]).filter(Boolean) : [];
    }

    // GetElem: coll[idx] → GetData (camel) and Get_Cast (snake); both valid
    if (head === "Get" || /GetElem/i.test(String(raw))) {
      const out = head ? [head] : [];
      const coll = [];
      const idx = [];
      for (const a of args) {
        const alts = go(a);
        if (!alts.length) continue;
        if (a.kind === "property" || a.kind === "method") coll.push(...alts);
        else idx.push(...alts);
      }
      const C = uniq(coll);
      const I = uniq(idx);
      for (const c of C) out.push(head + c); // GetData
      for (const i of I) out.push(head + "_" + i); // Get_Cast
      for (const c of C) {
        for (const i of I) out.push(head + c + "_" + i); // GetData_Cast
      }
      return uniq(out.filter(Boolean));
    }

    // ite: only the connective matters for paths (branch apps a x / b x → UFn noise)
    if (head === "Ite" || /^ite$/i.test(String(raw))) {
      return ["Ite"];
    }

    // Anonymous app: (f a b …) where f has explicit arity → BFn / UFn
    const isAnon =
      !head ||
      head === "Special" ||
      String(raw) === "[anonymous]" ||
      String(raw) === "anonymous";
    if (isAnon && args.length) {
      const fn = args[0];
      const rest = args.slice(1);
      const tag =
        fn?.kind === "symbol" ? fnArityTag(fn.type) : "";
      if (tag) {
        const interesting = rest
          .map(go)
          .filter((a) => a.length);
        if (!interesting.length) return [tag]; // σ b → UFn
        let acc = [tag];
        for (const alts of interesting) {
          acc = cartJoin(acc, alts, joinHeadChild);
        }
        return uniq(acc.filter(Boolean));
      }
      // unnamed/nested: fall through using remaining args only
      const restAlts = rest.map(go).filter((a) => a.length);
      if (restAlts.length) {
        return restAlts
          .reduce((acc, alts) => cartJoin(acc, alts, joinHeadChild), [""])
          .filter(Boolean);
      }
      return go(fn);
    }

    const argAlts = args.map(go).filter((a) => a.length);
    if (!argAlts.length) return head ? [head] : [];
    let acc = head ? [head] : [""];
    for (const alts of argAlts) {
      acc = cartJoin(acc, alts, joinHeadChild);
    }
    // bare head (drop arg detail) for ite / etc.
    return uniq([...acc, head].filter(Boolean));
  }

  if (node.body) return go(node.body);
  if (Array.isArray(node.args)) {
    const groups = node.args.map(go).filter((a) => a.length);
    if (!groups.length) return [];
    return groups.reduce((acc, alts) => cartJoin(acc, alts, (a, b) => a + b), [""]).filter(Boolean);
  }
  return [];
}

export function nameStruct(node) {
  return nameStructAlts(node)[0] || "";
}

/** All imply-path alternatives (exact strings). */
export function implyPathsFromStruct(struct) {
  const alts = nameStructAlts(struct).filter(
    (p) => p && !/\[anonymous\]|anonymous/i.test(p),
  );
  return alts.length ? alts : ["Imply"];
}

export function implyPathFromStruct(struct) {
  return implyPathsFromStruct(struct)[0];
}
