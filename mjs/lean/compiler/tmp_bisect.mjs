import { compile } from "../../../js/parser/lean.js";
import "../../../js/py.js";

function tryCompile(label, src) {
  try {
    compile(src);
    console.log("OK", label);
  } catch (e) {
    console.log("ERR", label, "=>", e.message.split("\n")[0]);
  }
}

const base = `import Mathlib
import Initialize.Tactic.Attr.Basic
open Rings


`;

const lemma = `/--
doc
-/
@[path]
lemma zero_eq_one_of_zero_isUnit
  {R : Type*}
  [Ring R]
-- given
  (h : IsUnit (0 : R)) :
-- imply
  (0 : R) = 1 := by
-- proof
  sorry
`;

tryCompile("no-ns", base + lemma + "\n-- created on 2026-10-23\n");
tryCompile("with-ns", base + "namespace Rings\n\n" + lemma + "\nend Rings\n\n-- created on 2026-10-23\n");
tryCompile("open-scoped", `import Mathlib
open scoped Classical

` + lemma);
tryCompile("ns-private", base + "namespace Rings\n\n/--\ndoc\n-/\n@[path]\nprivate lemma zero_eq_one_of_zero_isUnit\n  {R : Type*} [Ring R] : True := by\n  sorry\n\nend Rings\n");
tryCompile("attr-after-ns-open", `import Mathlib
namespace Rings
open Rings
/--
d
-/
@[path]
lemma foo : True := by trivial
end Rings
`);
