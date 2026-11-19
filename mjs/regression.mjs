import fs from "fs";
import path from "path";
import { fileURLToPath } from "url";
import { strStmt } from "../js/parser/lean/utility.js";
import { suggest, holeRegexAlternatives } from "./lemmaPath.mjs";

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const REPO = path.resolve(__dirname, "..");
const REG_DIR = path.join(__dirname, "regression");
const LEMMA_ROOT = path.join(REPO, "Lemma");

const norm = (s) => String(s || "")
  .split("\n")
  .filter((l) => !/^\s*--/.test(l))
  .join("\n")
  .replace(/\s+/g, "");
const loose = (s) => norm(s).replace(/[()]/g, "");

const eqFree = (regexes) => regexes.filter((re) => !String(re).includes("/eq/"));

function findNodeByText(root, text) {
  const target = loose(text);
  if (!target) return null;
  let hit = null;
  (function walk(n) {
    if (hit || !n || typeof n !== "object") return;
    if (Array.isArray(n)) {
      for (const x of n) walk(x);
      return;
    }
    let s = "";
    try { s = strStmt(n); } catch { s = ""; }
    if (s && loose(s) === target) {
      hit = n;
      return;
    }
    for (const a of n.args || []) walk(a);
  })(root);
  return hit;
}

let failures = 0;
const UPDATE = process.argv.includes("--update");
const files = fs.readdirSync(REG_DIR).filter((f) => f.endsWith(".json")).sort();
for (const name of files) {
  const doc = JSON.parse(fs.readFileSync(path.join(REG_DIR, name), "utf8"));
  const rel = name.replace(/\.json$/, "").split(".").join("/") + ".lean";
  const abs = path.join(LEMMA_ROOT, rel);
  const fail = (msg) => {
    failures++;
    console.log("FAIL " + name + "\n  " + msg);
  };
  if (!fs.existsSync(abs)) {
    fail("source not found: Lemma/" + rel);
    continue;
  }
  let r;
  try {
    r = suggest(abs, "main");
  } catch (e) {
    fail("suggest threw: " + e.message);
    continue;
  }
  const candidates = [
    {
      from: "imply",
      lean: r.implyLean,
      node: r.implyNode,
      opts: r.implyOpts,
      regexes: (r.imply || []).map((x) => x.regex),
    },
    ...(r.givens || []).map((gs, i) => ({
      from: "given[" + i + "]",
      lean: gs[0]?.lean,
      node: gs[0]?.node,
      opts: { ...r.implyOpts, asGiven: true },
      regexes: gs.map((x) => x.regex),
    })),
  ].filter((c) => c.lean);

  const target = norm(doc.lean);
  const score = (c) => {
    const s = norm(c.lean);
    if (!s || !target) return -1;
    if (s === target) return 3;
    if (s.endsWith(target)) return 2;
    if (s.includes(target)) return 1;
    const ls = loose(c.lean);
    const lt = loose(doc.lean);
    if (ls && lt && ls === lt) return 0.8;
    if (ls && lt && ls.includes(lt)) return 0.5;
    return -1;
  };
  const hit = candidates
    .map((c) => ({ c, score: score(c) }))
    .filter((x) => x.score >= 0)
    .sort((a, b) => b.score - a.score)[0];
  if (!hit) {
    fail("no imply/given matches lean:\n  " + doc.lean);
    continue;
  }

  let got;
  if (hit.score >= 2) {
    got = eqFree(hit.c.regexes);
  } else {
    const node = findNodeByText(hit.c.node, doc.lean);
    if (!node) {
      fail("no sub-expression of " + hit.c.from + " matches lean:\n  " + doc.lean);
      continue;
    }
    got = eqFree(holeRegexAlternatives(node, { ...hit.c.opts, skipCollectHoleAlternatives: true }));
  }

  if (JSON.stringify(got) !== JSON.stringify(doc.regex)) {
    if (UPDATE) {
      fs.writeFileSync(path.join(REG_DIR, name), JSON.stringify({ ...doc, regex: got }, null, 2) + "\n");
      console.log("updated " + name);
      continue;
    }
    fail(
      "regex drift (" + hit.c.from + ")\n  got:  " + JSON.stringify(got) +
      "\n  want: " + JSON.stringify(doc.regex),
    );
    continue;
  }
  console.log("ok   " + name);
}

console.log("\n" + (failures === 0 ? "all passed" : failures + " failed") + " (" + files.length + " fixtures)");
process.exit(failures === 0 ? 0 : 1);
