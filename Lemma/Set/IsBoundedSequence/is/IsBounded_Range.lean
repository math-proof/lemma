import Mathlib
import sympy.Basic
import sympy.analysis.Section_6_epilogue
open Filter
open Chapter6
open Chapter6.Sequence


/--
[Chapter6.Sequence.isBounded_iff_isBounded_range](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_epilogue.lean)
-/
@[path]
private lemma main
  {a:ℕ → ℝ} :
-- imply
  (a:Sequence).IsBounded ↔ Bornology.IsBounded (Set.range a) :=
-- proof
  Chapter6.Sequence.isBounded_iff_isBounded_range a


-- created on 2026-10-22
