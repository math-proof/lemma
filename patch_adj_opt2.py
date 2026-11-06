from pathlib import Path
p = Path("mjs/lemmaPath.mjs")
t = p.read_text()

old = '''    if (node.kind === "opt") {
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
    }'''

new = '''    if (node.kind === "opt") {
      const out = [];
      if (s[pos] === "_") out.push({ pos: pos + 1, edgeFilledOpt: false });
      const tryAt = (start) => {
        for (const m of matchSeq(node.alts || [], start, false)) {
          // Need sep before a following filled opt only if this fill does not
          // already end in `_` (same rule as enumerateHoleRegexLanguage).
          const endsWithHole = m.pos > 0 && s[m.pos - 1] === "_";
          out.push({ pos: m.pos, edgeFilledOpt: !endsWithHole });
        }
      };
      if (edgeFilledOpt) {
        // Previous filled opt ended on a non-`_` atom — require `_` sep (no glue).
        if (s[pos] === "_") tryAt(pos + 1);
      } else {
        tryAt(pos);
      }
      return out;
    }'''

if old not in t:
    raise SystemExit("opt match block missing")
p.write_text(t.replace(old, new, 1))
print("patched matcher")
