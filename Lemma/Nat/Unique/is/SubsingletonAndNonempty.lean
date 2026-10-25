import Mathlib
import sympy.Basic
import Theorem.Analysis.Tools.ExistsUnique.Part2


/--
[iff_subsingleton_nonempty](https://github.com/teorth/analysis/blob/main/Analysis/Tools/ExistsUnique.lean)
-/
@[path]
private lemma main
  {p: α → Prop} :
-- imply
  (∃! x, p x) ↔ (Subsingleton {x // p x} ∧ Nonempty {x // p x}) :=
-- proof
  ExistsUnique.iff_subsingleton_nonempty


-- created on 2026-10-20
