import Mathlib
import sympy.Basic
import sympy.analysis.Section_9_4
open Chapter9
open Chapter9.ContinuousWithinAt


/--
[ContinuousWithinAt.div'](https://github.com/teorth/analysis/blob/main/Analysis/Section_9_4.lean)
-/
@[path]
private lemma main
  {X:Set ℝ}
  {f g: ℝ → ℝ}
  {x₀:ℝ}
-- given
  (hM: g x₀ ≠ 0)
  (hf: ContinuousWithinAt f X x₀)
  (hg: ContinuousWithinAt g X x₀) :
-- imply
  ContinuousWithinAt (f / g) X x₀ :=
-- proof
  Chapter9.ContinuousWithinAt.div' f g hM hf hg


-- created on 2026-10-22
