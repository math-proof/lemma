import Mathlib
import sympy.Basic
import Abbrev.Analysis.Section_9_5.Part2
open Chapter9
open Chapter9.right_limit


/--
[right_limit.eq'](https://github.com/teorth/analysis/blob/main/Analysis/Section_9_5.lean)
-/
@[path]
private lemma main
  {X: Set ℝ}
  {f: ℝ → ℝ}
  {x₀:ℝ}
-- given
  (h: RightLimitExists X f x₀) :
-- imply
  (nhdsWithin x₀ (X ∩ .Ioi x₀)).Tendsto f (nhds (right_limit X f x₀)) :=
-- proof
  Chapter9.right_limit.eq' h


-- created on 2026-10-22
