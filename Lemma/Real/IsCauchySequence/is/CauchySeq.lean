import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_6_epilogue.Part2
open Filter
open Chapter6
open Chapter6.Sequence


/--
[Chapter6.Sequence.Cauchy_iff_CauchySeq](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_epilogue.lean)
-/
@[path]
private lemma main
  {a: ℕ → ℝ} :
-- imply
  (a:Sequence).IsCauchy ↔ CauchySeq a :=
-- proof
  Chapter6.Sequence.Cauchy_iff_CauchySeq a


-- created on 2026-10-22
