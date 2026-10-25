import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_9_4.Part2
open Chapter9
open Chapter9.ContinuousWithinAt


/--
[ContinuousWithinAt.max](https://github.com/teorth/analysis/blob/main/Analysis/Section_9_4.lean)
-/
@[path]
private lemma main
  {X:Set ℝ}
  {f g: ℝ → ℝ}
  {x₀:ℝ}
-- given
  (hf: ContinuousWithinAt f X x₀)
  (hg: ContinuousWithinAt g X x₀) :
-- imply
  ContinuousWithinAt (max f g) X x₀ :=
-- proof
  Chapter9.ContinuousWithinAt.max f g hf hg


-- created on 2026-10-22
