/**
 * suggestFromLean.mjs
 * ===================
 * Suggest lemma paths from a compiled lemma via Name.toJson imply.struct.
 *
 * Strategy:
 *   1. Path → `_private.Lemma.<…>.0.main`
 *   2. Enumerate ALL naming alts at each struct AST node
 *   3. Exact-match current path against that full set (consistency)
 *   4. Suggestions = alts whose files do NOT already exist (excl. current),
 *      sorted best→worst by ASCII byte length (shortest = least info)
 *
 * Usage:
 *   node mjs/suggestFromLean.mjs [--json] [--all] Lemma/.../Foo.lean
 *     --all  also list alts that already exist on disk
 */
import fs from "fs";
import path from "path";
import { fileURLToPath, pathToFileURL } from "url";
import { fetchLemmaJson } from "./fetchLemmaJson.mjs";
import { implyPathsFromStruct } from "./pathFromStruct.mjs";

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const REPO = path.resolve(__dirname, "..");

function normRel(p) {
  return String(p)
    .replace(/\\/g, "/")
    .replace(/^Lemma\//, "")
    .replace(/\.lean$/, "");
}

export function pathsExactMatch(existing, suggested) {
  return normRel(existing) === normRel(suggested);
}

function uniq(xs) {
  return [...new Set(xs.filter(Boolean))];
}

/** Drop junk tokens like Fun[anonymous]Val from Fin.val / anonymous apps. */
function isCleanPath(p) {
  return !/\[anonymous\]|anonymous/i.test(p);
}

/** Best = shortest ASCII bytes; worst = longest (redundant). Tie-break lexicographic. */
function byBestToWorst(a, b) {
  const ba = Buffer.byteLength(a, "utf8");
  const bb = Buffer.byteLength(b, "utf8");
  if (ba !== bb) return ba - bb;
  return a < b ? -1 : a > b ? 1 : 0;
}

/**
 * Enumeration/verdict from an already-fetched `Name.toJson` payload, so a batch scan
 * (`mjs/scanLemmaPaths.mjs --batch`) can reuse it without spawning Lean per file.
 *
 * @param {object} json `Name.toJson` payload of the private main lemma
 * @param {string} relPath module path relative to the repo, e.g. `Lemma/Set/Foo.lean`
 */
export function suggestFromJson(json, relPath) {
  const rel = String(relPath).replace(/\\/g, "/").replace(/\.lean$/, "");
  const imply = json.imply || {};
  const struct = imply.struct;
  if (!struct) throw new Error("imply.struct missing in Name.toJson for " + rel);

  const implyAlts = implyPathsFromStruct(struct).filter(isCleanPath);
  const parts = normRel(rel).split("/").filter(Boolean);
  const section = parts[0];

  const givenArr = Array.isArray(json.given) ? json.given : [];
  const givenAltLists = givenArr
    .map((g) => (g?.struct ? implyPathsFromStruct(g.struct).filter(isCleanPath) : []))
    .filter((a) => a.length)
    .reverse();
  const givenNames = givenAltLists.map((a) => a[0]);
  function cartGiven(lists) {
    if (!lists.length) return [""];
    return lists.reduce(
      (acc, alts) => acc.flatMap((p) => alts.map((a) => (p ? p + "/" + a : a))),
      [""],
    );
  }
  const givenPaths = cartGiven(givenAltLists);

  const allSuggestions = uniq(
    implyAlts.flatMap((implyPath) =>
      givenPaths.map((givenPath) => {
        const body = givenPath
          ? `${section}/${implyPath}/of/${givenPath}.lean`
          : `${section}/${implyPath}.lean`;
        return body.replace(/\\/g, "/");
      }),
    ),
  )
    .filter(isCleanPath)
    .sort(byBestToWorst);

  const currentPath = normRel(rel) + ".lean";
  const matchedSuggestion =
    allSuggestions.find((s) => pathsExactMatch(currentPath, s)) || null;

  const existingOnDisk = [];
  const suggestions = [];
  for (const s of allSuggestions) {
    if (pathsExactMatch(currentPath, s)) continue;
    const fileAbs = path.join(REPO, "Lemma", s);
    if (fs.existsSync(fileAbs)) existingOnDisk.push(s);
    else suggestions.push(s);
  }

  return {
    source: "lean-Name.toJson",
    currentPath,
    allSuggestions,
    suggestions,
    existingOnDisk,
    consistent: matchedSuggestion != null,
    matchedSuggestion,
    implyAlts: [...implyAlts].sort(byBestToWorst),
    givensPathOrder: givenNames,
    lean: imply.lean,
    latex: imply.latex,
  };
}

/** One-shot wrapper: fetch `Name.toJson` for `Lemma/….lean`, then apply `suggestFromJson`. */
export function suggestFromLean(leanFile) {
  const abs = path.resolve(leanFile);
  const rel = path.relative(REPO, abs).replace(/\\/g, "/");
  const { name, json, moduleName } = fetchLemmaJson(abs);
  return { ...suggestFromJson(json, rel), privateMain: name, moduleName };
}

const argv = process.argv.slice(2);
const asJson = argv.includes("--json");
const showAll = argv.includes("--all");
const file = argv.find((a) => !a.startsWith("-"));
const isMain =
  process.argv[1] &&
  pathToFileURL(path.resolve(process.argv[1])).href === import.meta.url;

if (isMain) {
  if (!file) {
    console.error(
      "Usage: node mjs/suggestFromLean.mjs [--json] [--all] <Lemma/.../Foo.lean>",
    );
    process.exit(1);
  }
  try {
    const r = suggestFromLean(file);
    if (asJson) console.log(JSON.stringify(r, null, 2));
    else {
      console.log("source:     " + r.source);
      console.log("private:    " + r.privateMain);
      console.log("current:    Lemma/" + r.currentPath);
      console.log(
        "consistent: " +
          (r.consistent ? "yes (exact match)" : "no"),
      );
      if (r.matchedSuggestion)
        console.log(
          "matched:    Lemma/" +
            r.matchedSuggestion +
            " (" +
            Buffer.byteLength(r.matchedSuggestion, "utf8") +
            " B)",
        );
      console.log(
        "suggestions (" +
          r.suggestions.length +
          ", best→worst by ASCII bytes, paths not on disk):",
      );
      if (!r.suggestions.length) console.log("  (none)");
      for (const s of r.suggestions) {
        console.log(
          "  - Lemma/" + s + "  [" + Buffer.byteLength(s, "utf8") + " B]",
        );
      }
      if (showAll) {
        console.log(
          "all alts including existing (" + r.allSuggestions.length + "):",
        );
        for (const s of r.allSuggestions) {
          const tags = [];
          if (s === r.matchedSuggestion) tags.push("current");
          if (r.existingOnDisk.includes(s)) tags.push("exists");
          const mark = tags.length ? " (" + tags.join(", ") + ")" : "";
          console.log(
            "  - Lemma/" +
              s +
              "  [" +
              Buffer.byteLength(s, "utf8") +
              " B]" +
              mark,
          );
        }
      } else if (r.existingOnDisk.length) {
        console.log(
          "omitted " +
            r.existingOnDisk.length +
            " alt(s) that already exist (pass --all to show)",
        );
      }
    }
  } catch (e) {
    console.error(e.message || e);
    process.exit(1);
  }
}
