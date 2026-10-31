/**
 * Shared helpers for Node#pathChoices / Lean* polymorphic overrides
 * (lemma-path MulInvSqrt factor walk). No cls(name) dispatch here —
 * LeanColon / LeanProperty / LeanParenthesis / LeanMul / LeanDiv /
 * LeanInv / Lean_sqrt / LeanEq implement pathChoices / pathImplyStems.
 */

/** Like Set-uniq but keeps empty-string omit markers. */
export function pathUniqKeepEmpty(xs) {
  const out = [];
  const seen = new Set();
  for (const x of xs || []) {
    const k = x === "" ? "\0omit" : x;
    if (seen.has(k)) continue;
    seen.add(k);
    out.push(x);
  }
  return out;
}

export function pathUniq(xs) {
  return [...new Set((xs || []).filter(Boolean))];
}

/** Trailing hole underscores (kept through emit/combine; stripped only at Eq root). */
export function pathTrailingHoles(s) {
  const m = /_+$/.exec(String(s || ""));
  return m ? m[0].length : 0;
}

export function pathStripTrailingHoles(s) {
  return String(s || "").replace(/_+$/, "");
}

/**
 * Mul Op(LHS)(RHS) factor combine.
 * Both holes → Mul__; Sqrt+Div → MulSqrt_Div; right-omit keeps Mul's trailing `_`.
 */
export function pathCombineMulChoices(leftChoices, rightChoices) {
  const L = leftChoices || [""];
  const R = rightChoices || [""];
  const out = [];
  for (const l of L) {
    for (const r of R) {
      if (!l && !r) out.push("Mul__");
      else if (l && r) {
        const lCore = pathStripTrailingHoles(l);
        if (/Sqrt$/.test(lCore) && /^Div/.test(r)) out.push("Mul" + lCore + "_" + r);
        else out.push("Mul" + l + r);
      } else if (l) {
        out.push("Mul" + l + "_"); // Mul's right hole — never strip here
      } else {
        out.push("Mul_" + r);
      }
    }
  }
  return pathUniq(out);
}


/**
 * Flat Eq Op(LHS)(RHS). Mul×Mul → null (skip EqMulS; Mul/eq/Mul covers).
 * GtMulS is untouched (different family / not emitted here).
 */
export function pathEqFlatStem(lhs, rhs) {
  const lH = pathTrailingHoles(lhs);
  const L = pathStripTrailingHoles(lhs);
  const R = pathStripTrailingHoles(rhs);
  if (L === "Mul" && R === "Mul") return null;
  let join;
  if (R === "Mul") join = "_".repeat(Math.max(1, lH));
  else if (L === "Mul") join = "__";
  else join = "__";
  return "Eq" + L + join + R;
}

/**
 * Eq root infix combine: slash LHS.eq.RHS + flat Op(LHS)(RHS);
 * strip trailing `_` only here.
 */
export function pathEqCombineChoices(leftChoices, rightChoices, house = "") {
  const leftRaw = (leftChoices || []).filter((s) => /^Mul/.test(s || ""));
  const rightRaw = (rightChoices || []).filter((s) => /^Mul/.test(s || ""));
  const left = pathUniq(leftRaw.map(pathStripTrailingHoles));
  const right = pathUniq(rightRaw.map(pathStripTrailingHoles));
  const soft = "eq";
  const slash = [];
  const flats = [];
  for (const lRaw of leftRaw) {
    for (const rRaw of rightRaw) {
      const l = pathStripTrailingHoles(lRaw);
      const r = pathStripTrailingHoles(rRaw);
      slash.push(l + "/" + soft + "/" + r);
      const flat = pathEqFlatStem(lRaw, rRaw);
      if (flat) flats.push(flat);
    }
  }
  const houseN = String(house || "").replace(/\\/g, "/");
  const slashU = pathUniq(slash);
  const slashRest = slashU
    .filter((s) => s !== houseN)
    .sort((a, b) => a.length - b.length || (a < b ? -1 : a > b ? 1 : 0));
  const flatSorted = pathUniq(flats).sort((a, b) => a.length - b.length || (a < b ? -1 : a > b ? 1 : 0));
  const orderedSlash = slashU.includes(houseN)
    ? [houseN, ...slashRest]
    : [...slashU].sort((a, b) => a.length - b.length || (a < b ? -1 : a > b ? 1 : 0));
  return { left, right, leftRaw, rightRaw, stems: [...orderedSlash, ...flatSorted], soft };
}
