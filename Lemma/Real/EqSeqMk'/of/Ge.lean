import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.Section_7_2.Part5
open Chapter7


/--
[eval_mk'](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_2.lean)
-/
@[path]
private lemma main
  {m:ℤ}
  {a : { n // n ≥ m } → ℝ}
  {n : ℤ}
-- given
  (h:n ≥ m) :
-- imply
  (Series.mk' a).seq n = a ⟨ n, h ⟩ :=
-- proof
  Chapter7.Series.eval_mk' a h


-- created on 2026-10-20
