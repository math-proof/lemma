import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_6_epilogue.Part2
open Filter
open Chapter6
open Chapter6.Sequence


/--
[Chapter6.Sequence.tendsto_iff_Tendsto](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_epilogue.lean)
-/
@[path]
private lemma main
  {a: ℕ → ℝ}
  {L:ℝ} :
-- imply
  (a:Sequence).TendsTo L ↔ atTop.Tendsto a (nhds L) :=
-- proof
  Chapter6.Sequence.tendsto_iff_Tendsto a L


-- created on 2026-10-22
