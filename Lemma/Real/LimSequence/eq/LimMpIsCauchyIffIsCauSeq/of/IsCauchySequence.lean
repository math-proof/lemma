import Mathlib
import sympy.Basic
import sympy.analysis.Section_6_epilogue
open Filter
open Chapter6
open Chapter6.Sequence


/--
[Chapter6.Sequence.lim_eq_CauSeq_lim](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_epilogue.lean)
-/
@[path]
private lemma main
  {a:ℕ → ℝ}
-- given
  (ha: (a:Sequence).IsCauchy) :
-- imply
  Chapter6.lim (a:Sequence) = CauSeq.lim  ⟨ a, (isCauchy_iff_isCauSeq a).mp ha⟩ :=
-- proof
  Chapter6.Sequence.lim_eq_CauSeq_lim a ha


-- created on 2026-10-22
