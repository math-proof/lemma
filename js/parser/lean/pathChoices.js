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
        const rCore = pathStripTrailingHoles(r);
        // 𝔼 * 𝔼 → MulExpectS (plural). Not MulExpectExpect.
        if (lCore === "Expect" && rCore === "Expect") out.push("MulExpectS");
        else if (/Sqrt$/.test(lCore) && /^Div/.test(r)) out.push("Mul" + lCore + "_" + r);
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
  // Omitted LHS is one hole: Eq_MulExpectS, not Eq__MulExpectS.
  // RHS Mul keeps a holed LHS's trailing `_` as the join (Expect_Mul__ → EqExpect_Mul__Mul).
  // No holes on the LHS: Eq(Expect)(Mul) is EqExpect__Mul, same `__` as Eq(Expect)(MulExpect).
  if (!L) join = "_";
  else if (R === "Mul") join = lH ? "_".repeat(lH) : "__";
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

/**
 * Eq infix for any side choices, including omit (`""`).
 * Both sides named → `LHS/eq/RHS`. Flat form is `Eq(LHS)(RHS)` (`pathEqFlatStem`, trailing `_` stripped).
 * Both-omit is dropped (`Eq` alone is not a side pair).
 */
export function pathEqInfixChoices(leftChoices, rightChoices, house = "") {
  const leftRaw = pathUniqKeepEmpty(leftChoices || [""]);
  const rightRaw = pathUniqKeepEmpty(rightChoices || [""]);
  const slash = [];
  const flats = [];
  for (const lRaw of leftRaw) {
    for (const rRaw of rightRaw) {
      const l = pathStripTrailingHoles(lRaw);
      const r = pathStripTrailingHoles(rRaw);
      if (l && r) slash.push(l + "/eq/" + r);
      if (!l && !r) continue;
      const flat = pathEqFlatStem(lRaw, rRaw);
      if (flat) flats.push(pathStripTrailingHoles(flat));
    }
  }
  const byLen = (a, b) => a.length - b.length || (a < b ? -1 : a > b ? 1 : 0);
  const slashU = pathUniq(slash);
  const flatU = pathUniq(flats).filter((s) => !slashU.includes(s));
  const houseN = String(house || "").replace(/\\/g, "/");
  const slashRest = slashU.filter((s) => s !== houseN).sort(byLen);
  const flatRest = flatU.filter((s) => s !== houseN).sort(byLen);
  const head = slashU.includes(houseN) || flatU.includes(houseN) ? [houseN] : [];
  return {
    left: pathUniq(leftRaw.map(pathStripTrailingHoles)),
    right: pathUniq(rightRaw.map(pathStripTrailingHoles)),
    stems: pathUniq([...head, ...slashRest, ...flatRest]),
    soft: "eq",
  };
}


/**
 * Flat And Op(LHS)(RHS). Same hole join as Eq (`pathEqFlatStem`).
 * Both arguments omitted → `And__` (two holes), not `And_`.
 */
export function pathAndFlatStem(lhs, rhs) {
  const L = pathStripTrailingHoles(lhs);
  const R = pathStripTrailingHoles(rhs);
  if (!L && !R) return "And__";
  const stem = pathEqFlatStem(lhs, rhs);
  if (!stem || !stem.startsWith("Eq")) return null;
  return "And" + stem.slice(2);
}

/**
 * And infix for any side choices, including omit (`""`).
 * Both sides named → `LHS/and/RHS`. Flat form is `And(LHS)(RHS)`.
 * Both-omit is `And__`.
 * @param {string[]} leftChoices
 * @param {string[]} rightChoices
 * @param {string} [house]
 */
export function pathAndInfixChoices(leftChoices, rightChoices, house = "") {
  const leftRaw = pathUniqKeepEmpty(leftChoices || [""]);
  const rightRaw = pathUniqKeepEmpty(rightChoices || [""]);
  const slash = [];
  const flats = [];
  for (const lRaw of leftRaw) {
    for (const rRaw of rightRaw) {
      const l = pathStripTrailingHoles(lRaw);
      const r = pathStripTrailingHoles(rRaw);
      if (l && r) slash.push(l + "/and/" + r);
      if (!l && !r) {
        flats.push("And__");
        continue;
      }
      const flat = pathAndFlatStem(lRaw, rRaw);
      if (flat) flats.push(flat === "And__" ? flat : pathStripTrailingHoles(flat));
    }
  }
  const byLen = (a, b) => a.length - b.length || (a < b ? -1 : a > b ? 1 : 0);
  const slashU = pathUniq(slash);
  const flatU = pathUniq(flats).filter((s) => !slashU.includes(s));
  const houseN = String(house || "").replace(/\\/g, "/");
  const slashRest = slashU.filter((s) => s !== houseN).sort(byLen);
  const flatRest = flatU.filter((s) => s !== houseN).sort(byLen);
  const head = slashU.includes(houseN) || flatU.includes(houseN) ? [houseN] : [];
  return {
    left: pathUniq(leftRaw.map(pathStripTrailingHoles)),
    right: pathUniq(rightRaw.map(pathStripTrailingHoles)),
    stems: pathUniq([...head, ...slashRest, ...flatRest]),
    soft: "and",
  };
}

/**
 * Flat Imp Op(LHS)(RHS). Same hole join as Eq/And (`pathEqFlatStem`).
 * Both arguments omitted → `Imp__` (two holes), not `Imp_`.
 */
export function pathImpFlatStem(lhs, rhs) {
  const L = pathStripTrailingHoles(lhs);
  const R = pathStripTrailingHoles(rhs);
  if (!L && !R) return "Imp__";
  const stem = pathEqFlatStem(lhs, rhs);
  if (!stem || !stem.startsWith("Eq")) return null;
  return "Imp" + stem.slice(2);
}

/**
 * Imp (`→`) infix for any side choices, including omit (`""`).
 * Both sides named → `LHS/imp/RHS`. Flat form is `Imp(LHS)(RHS)`.
 * Both-omit is `Imp__`. Parallel to And (`pathAndInfixChoices`).
 * @param {string[]} leftChoices
 * @param {string[]} rightChoices
 * @param {string} [house]
 */
export function pathImpInfixChoices(leftChoices, rightChoices, house = "") {
  const leftRaw = pathUniqKeepEmpty(leftChoices || [""]);
  const rightRaw = pathUniqKeepEmpty(rightChoices || [""]);
  const slash = [];
  const flats = [];
  for (const lRaw of leftRaw) {
    for (const rRaw of rightRaw) {
      const l = pathStripTrailingHoles(lRaw);
      const r = pathStripTrailingHoles(rRaw);
      if (l && r) slash.push(l + "/imp/" + r);
      if (!l && !r) {
        flats.push("Imp__");
        continue;
      }
      const flat = pathImpFlatStem(lRaw, rRaw);
      if (flat) flats.push(flat === "Imp__" ? flat : pathStripTrailingHoles(flat));
    }
  }
  const byLen = (a, b) => a.length - b.length || (a < b ? -1 : a > b ? 1 : 0);
  const slashU = pathUniq(slash);
  const flatU = pathUniq(flats).filter((s) => !slashU.includes(s));
  const houseN = String(house || "").replace(/\\/g, "/");
  const slashRest = slashU.filter((s) => s !== houseN).sort(byLen);
  const flatRest = flatU.filter((s) => s !== houseN).sort(byLen);
  const head = slashU.includes(houseN) || flatU.includes(houseN) ? [houseN] : [];
  return {
    left: pathUniq(leftRaw.map(pathStripTrailingHoles)),
    right: pathUniq(rightRaw.map(pathStripTrailingHoles)),
    stems: pathUniq([...head, ...slashRest, ...flatRest]),
    soft: "imp",
  };
}

/**
 * IndepFun `⟂ᵢ` infix combine (binary op like Mul/Eq): LHS.Indep.RHS.
 * Hole sides omit; a GetSlice operand yields Indep_GetSlice (right) /
 * IndepGetSlice (left, camel — parallel IndepJoint / Indep_Joint).
 */
export function pathCombineIndepChoices(leftChoices, rightChoices) {
  const L = pathUniqKeepEmpty(leftChoices || [""]);
  const R = pathUniqKeepEmpty(rightChoices || [""]);
  const out = [];
  for (const l of L) {
    for (const r of R) {
      if (l && r) out.push("Indep" + l + "_" + r);
      else if (!l && r) out.push("Indep_" + r);
      else if (l && !r) out.push("Indep" + l);
    }
  }
  // bare Indep last so richer operand spellings rank first
  if (L.some((x) => !x) && R.some((x) => !x)) out.push("Indep");
  if (!out.length) out.push("Indep");
  return pathUniq(out);
}


/* -------------------------------------------------------------------------- */
/* holeRegex helpers (Body t366) — polymorphic Node#holeRegex composition     */
/* lemmaPath should call `node.holeRegex(opts)` instead of a cls()-switch.    */
/* Plural MulS alt stays in lemmaPath (`pluralMulSHoleRegex`), not here.      */
/* -------------------------------------------------------------------------- */

/** Escape a literal fragment for an imply hole-regex. */
export function escapeHoleReLit(s) {
  return String(s || "").replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
}

/**
 * Wrap a filled child as an optional hole alternative: (_|filled).
 * Empty/missing children are a bare hole `_`.
 * @param {string|null|undefined} filled
 * @returns {string}
 */
export function wrapHoleOpt(filled) {
  if (filled == null || filled === "") return "_";
  return "(_|" + filled + ")";
}

/** Stored group `(Fill)`. Empty is the hole `_`. `consistent` expands `(` to `(_|`. */
export function storedHoleOpt(frag) {
  if (frag == null || frag === "") return "_";
  return "(" + frag + ")";
}

/** Trig/log heads for LeanProperty / ArgsSpaceSeparated apps. */
export const HOLE_RE_TRIG_FN = /^(sin|cos|tan|cot|arctan|log|exp)$/i;

/**
 * Minimal CamelCase token name (sin→Sin). lemmaPath may pass `opts.nameToken`
 * with the full SYMBOL_NAME / TOKEN_ALIAS pass.
 * @param {string} text
 * @returns {string}
 */
export function holeRegexDefaultNameToken(text) {
  if (!text) return "";
  let s = String(text);
  if (s.includes(".")) s = s.slice(s.lastIndexOf(".") + 1);
  if (!s || s === "_" || s === "[anonymous]" || s === "anonymous") return "";
  if (s.includes("_"))
    s = s.split("_").map((p) => (p ? p.charAt(0).toUpperCase() + p.slice(1) : "")).join("");
  else
    s = s.charAt(0).toUpperCase() + s.slice(1);
  return s.replace(/[^\x00-\x7F]/g, "").replace(/\*+$/, "");
}

/** @param {object|null|undefined} node @param {object} [opts] @returns {string|null} */
export function holeRegexChild(node, opts = {}) {
  if (!node) return null;
  // Peel display wrappers so binary Imp/And/Eq children keep structured holeRegex
  // (newline-wrapped antecedent of `P → Q` under ∀ᵐ must not freeze via nameExpr).
  let n = node;
  for (let i = 0; i < 8 && n; i++) {
    const c = n.constructor?.name || "";
    if (c === "LeanParenthesis") {
      n = n.arg ?? n.args?.[0];
      continue;
    }
    if (c === "LeanStatements" || c === "LeanArgsNewLineSeparated") {
      const args = n.args || [];
      n = args.find((a) => (a?.constructor?.name || "") !== "LeanLineComment") || args[0];
      continue;
    }
    if (c === "LeanColon") {
      n = n.args?.[0];
      continue;
    }
    break;
  }
  if (!n || typeof n.holeRegex !== "function") return null;
  const frag = n.holeRegex(opts);
  return frag == null || frag === "" ? null : frag;
}

function holeRegexPeelParen(n) {
  let x = n;
  for (let i = 0; i < 6 && x; i++) {
    if (x.constructor?.name === "LeanParenthesis") {
      x = x.arg ?? x.args?.[0];
      continue;
    }
    break;
  }
  return x;
}

/** Structural √ / `.sqrt` probe for Mul(Sqrt, Div) join underscore. */
export function holeRegexIsSqrtNode(n) {
  const x = holeRegexPeelParen(n);
  if (!x) return false;
  if (x.constructor?.name === "Lean_sqrt") return true;
  if (x.constructor?.name === "LeanProperty") {
    const p = x.rhs ?? x.args?.[1];
    return (p?.text || "") === "sqrt";
  }
  return false;
}

/** Structural Div probe for Mul(Sqrt, Div) join underscore. */
export function holeRegexIsDivNode(n) {
  const x = holeRegexPeelParen(n);
  return x?.constructor?.name === "LeanDiv";
}

/**
 * Binary arithmetic hole-regex (Add/Sub/Mul/Div/Pow/Dot).
 * @param {string} tag
 * @param {object|null} leftNode
 * @param {object|null} rightNode
 * @param {object} [opts]
 * @param {{ isMul?: boolean, subscript?: string }} [mul]
 * @returns {string|null}
 */
export function holeRegexCombineArith(tag, leftNode, rightNode, opts = {}, mul = null) {
  const L = holeRegexChild(leftNode, opts);
  const R = rightNode != null ? holeRegexChild(rightNode, opts) : null;
  const lHole = L == null || L === "";
  const rHole = R == null || R === "";
  const isMul = !!(mul && mul.isMul);
  if (!lHole && !rHole) {
    if (isMul && holeRegexIsSqrtNode(leftNode) && holeRegexIsDivNode(rightNode))
      return tag + wrapHoleOpt(L) + "_" + wrapHoleOpt(R);
    return tag + wrapHoleOpt(L) + wrapHoleOpt(R);
  }
  if (!lHole && rHole) {
    if (isMul && /^(?:T|Adjoint|Conj)$/.test(L)) return tag + L + "__";
    if (/^-?\d+$/.test(L)) return tag + wrapHoleOpt(L) + "_";
    if (/[(|]/.test(L)) return tag + wrapHoleOpt(L) + "_";
    return tag + L;
  }
  if (lHole && !rHole) return tag + "_" + wrapHoleOpt(R);
  if (isMul && mul.subscript === "ᵥ") return tag + "__";
  if (isMul) return opts.mulBothHolesBare ? tag : tag + "(_)" + "(_)";
  return tag;
}

/**
 * Relational / iff / subset / dvd hole-regex (Eq/Ne/Lt/…).
 * @param {string} tag
 * @param {object|null} leftNode
 * @param {object|null} rightNode
 * @param {object} [opts]
 * @returns {string|null}
 */
export function holeRegexCombineRel(tag, leftNode, rightNode, opts = {}) {
  const L = holeRegexChild(leftNode, opts);
  const R = holeRegexChild(rightNode, opts);
  const lHole = L == null || L === "";
  const rHole = R == null || R === "";
  if (lHole && !rHole) return tag + "_" + wrapHoleOpt(R);
  if (!lHole && rHole) return tag + wrapHoleOpt(L);
  if (!lHole && !rHole) return tag + wrapHoleOpt(L) + wrapHoleOpt(R);
  return tag;
}

/**
 * Unary Neg/Inv/Sqrt-style hole-regex.
 * @param {string} tag
 * @param {object|null} argNode
 * @param {object} [opts]
 * @returns {string|null}
 */
export function holeRegexCombineUnary(tag, argNode, opts = {}) {
  const inner = holeRegexChild(argNode, opts);
  if (inner == null || inner === "") return tag;
  return tag + wrapHoleOpt(inner);
}

/**
 * Binary Nat.choose / d.choose -> Binom (Body / Cosmos).
 * Filled left + hole right: Binom((Mul(_|2)_)_) -- required group around left
 * fill (same paren style as Deriv_(scope)), then second-arg hole.
 * @param {object|null} leftNode
 * @param {object|null} rightNode
 * @param {object} [opts]
 * @returns {string}
 */
export function holeRegexCombineBinom(leftNode, rightNode, opts = {}) {
  const L = holeRegexChild(leftNode, opts);
  const R = rightNode != null ? holeRegexChild(rightNode, opts) : null;
  const lHole = L == null || L === "";
  const rHole = R == null || R === "";
  if (!lHole && rHole) return "Binom((" + L + ")_)";
  if (lHole && !rHole) return "Binom(_" + wrapHoleOpt(R) + ")";
  if (!lHole && !rHole) return "Binom((" + L + ")" + wrapHoleOpt(R) + ")";
  return "Binom__";
}

