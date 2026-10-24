import Mathlib
import sympy.Basic
import sympy.analysis.Section_9_5
open Chapter9
open Chapter9.left_limit


/--
[left_limit.eq'](https://github.com/teorth/analysis/blob/main/Analysis/Section_9_5.lean)
-/
@[path]
private lemma main
  {X: Set ℝ}
  {f: ℝ → ℝ}
  {x₀:ℝ}
-- given
  (h: LeftLimitExists X f x₀) :
-- imply
  (nhdsWithin x₀ (X ∩ .Iio x₀)).Tendsto f (nhds (left_limit X f x₀)) :=
-- proof
  Chapter9.left_limit.eq' h


-- created on 2026-10-22
