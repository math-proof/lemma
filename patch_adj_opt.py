from pathlib import Path

p = Path("mjs/lemmaPath.mjs")
t = p.read_text()

old_enum = '''export function enumerateHoleRegexLanguage(reSource) {
  const parts = parseHoleRegexTree(reSource);
  function cart(nodes) {
    let acc = [""];
    for (const p of nodes || []) {
      const next = [];
      if (p.kind === "lit") {
        for (const a of acc) next.push(a + p.v);
      } else if (p.kind === "hole") {
        for (const a of acc) next.push(a + "_");
      } else if (p.kind === "opt") {
        const filled = cart(p.alts);
        for (const a of acc) {
          next.push(a + "_");
          for (const f of filled) next.push(a + f);
        }
      } else if (p.kind === "group") {
        const inner = cart(p.kids);
        for (const a of acc) for (const f of inner) next.push(a + f);
      }
      acc = next.length ? next : acc;
      if (acc.length > 20000) break;
    }
    return acc;
  }
  try {
    return cart(parts);
  } catch {
    return [];
  }
}'''

new_enum = '''export function enumerateHoleRegexLanguage(reSource) {
  const parts = parseHoleRegexTree(reSource);
  /**
   * Cartesian expand. Adjacent filled optional siblings get `_` between them
   * (SinDiv…Pi + CosAdd… → Pi_Cos, not PiCos). Omit `_` does not invent extras.
   * Acc entries: { s, edgeFilledOpt } — edgeFilledOpt means last sibling chose opt-fill.
   */
  function cart(nodes) {
    let acc = [{ s: "", edgeFilledOpt: false }];
    for (const p of nodes || []) {
      const next = [];
      if (p.kind === "lit") {
        for (const a of acc) next.push({ s: a.s + p.v, edgeFilledOpt: false });
      } else if (p.kind === "hole") {
        for (const a of acc) next.push({ s: a.s + "_", edgeFilledOpt: false });
      } else if (p.kind === "opt") {
        const filled = cart(p.alts);
        for (const a of acc) {
          next.push({ s: a.s + "_", edgeFilledOpt: false });
          for (const f of filled) {
            if (!f.s) continue;
            const sep =
              a.edgeFilledOpt && !a.s.endsWith("_") && !f.s.startsWith("_") ? "_" : "";
            next.push({ s: a.s + sep + f.s, edgeFilledOpt: true });
          }
        }
      } else if (p.kind === "group") {
        const inner = cart(p.kids);
        for (const a of acc) {
          for (const f of inner) {
            const sep =
              a.edgeFilledOpt &&
              f.edgeFilledOpt &&
              f.s &&
              !a.s.endsWith("_") &&
              !f.s.startsWith("_")
                ? "_"
                : "";
            next.push({
              s: a.s + sep + f.s,
              edgeFilledOpt: f.edgeFilledOpt,
            });
          }
        }
      }
      acc = next.length ? next : acc;
      if (acc.length > 20000) break;
    }
    return acc;
  }
  try {
    return cart(parts).map((a) => a.s);
  } catch {
    return [];
  }
}'''

if old_enum not in t:
    raise SystemExit("enumerate block not found")
t = t.replace(old_enum, new_enum, 1)
print("patched enumerate")

old_consistent = '''export function consistent(token, regex, depth) {
  const src = String(regex || "");
  if (!src) return false;
  const d = Math.max(0, Number(depth) || 0);
  const t =
    normalizeHouseEqTokenToRegex(String(token || "").replace(/'/g, ""), src) +
    "_".repeat(d);
  try {
    return new RegExp("^" + src + "_*$").test(t);
  } catch {
    return false;
  }
}'''

new_consistent = '''/**
 * Match token against hole-regex tree. Adjacent filled optional siblings require
 * a separating `_` (same rule as enumerateHoleRegexLanguage). Trailing `_` ok.
 * @returns {boolean}
 */
function matchHoleRegexTreeToken(nodes, token) {
  const s = String(token || "");
  /** @returns {{ pos: number, edgeFilledOpt: boolean }[]} */
  function matchSeq(seq, pos, edgeFilledOpt) {
    if (!seq.length) return [{ pos, edgeFilledOpt }];
    const [head, ...rest] = seq;
    const heads = matchNode(head, pos, edgeFilledOpt);
    const out = [];
    for (const h of heads) {
      for (const r of matchSeq(rest, h.pos, h.edgeFilledOpt)) out.push(r);
    }
    return out;
  }
  /** @returns {{ pos: number, edgeFilledOpt: boolean }[]} */
  function matchNode(node, pos, edgeFilledOpt) {
    if (!node) return [];
    if (node.kind === "lit") {
      const v = node.v || "";
      if (v && s.startsWith(v, pos)) return [{ pos: pos + v.length, edgeFilledOpt: false }];
      if (!v) return [{ pos, edgeFilledOpt }];
      return [];
    }
    if (node.kind === "hole") {
      if (s[pos] === "_") return [{ pos: pos + 1, edgeFilledOpt: false }];
      return [];
    }
    if (node.kind === "opt") {
      const out = [];
      if (s[pos] === "_") out.push({ pos: pos + 1, edgeFilledOpt: false });
      const tryAt = (start) => {
        for (const m of matchSeq(node.alts || [], start, false)) {
          out.push({ pos: m.pos, edgeFilledOpt: true });
        }
      };
      if (edgeFilledOpt) {
        // Require `_` between adjacent filled opts — reject glued PiCos forms.
        if (s[pos] === "_") tryAt(pos + 1);
      } else {
        tryAt(pos);
      }
      return out;
    }
    if (node.kind === "group") {
      return matchSeq(node.kids || [], pos, edgeFilledOpt);
    }
    return [];
  }
  const ends = matchSeq(nodes || [], 0, false);
  return ends.some((e) => e.pos <= s.length && /^_*$/.test(s.slice(e.pos)));
}

export function consistent(token, regex, depth) {
  const src = String(regex || "");
  if (!src) return false;
  const d = Math.max(0, Number(depth) || 0);
  const t =
    normalizeHouseEqTokenToRegex(String(token || "").replace(/'/g, ""), src) +
    "_".repeat(d);
  const tree = parseHoleRegexTree(src);
  if (tree.length) {
    try {
      return matchHoleRegexTreeToken(tree, t);
    } catch {
      /* fall through */
    }
  }
  try {
    return new RegExp("^" + src + "_*$").test(t);
  } catch {
    return false;
  }
}'''

if old_consistent not in t:
    raise SystemExit("consistent block not found")
t = t.replace(old_consistent, new_consistent, 1)
print("patched consistent")

p.write_text(t)
print("WROTE")
