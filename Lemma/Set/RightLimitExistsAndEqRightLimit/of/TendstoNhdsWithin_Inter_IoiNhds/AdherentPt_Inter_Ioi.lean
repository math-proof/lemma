import Mathlib
import sympy.Basic
import Abbrev.Analysis.Section_9_5.Part2
open Chapter9
open Chapter9.right_limit


/--
[right_limit.eq](https://github.com/teorth/analysis/blob/main/Analysis/Section_9_5.lean)
-/
@[path]
private lemma main
  {X: Set ℝ}
  {f: ℝ → ℝ}
  {x₀ L : ℝ}
-- given
  (had: AdherentPt x₀ (X ∩ .Ioi x₀))
  (h: (nhdsWithin x₀ (X ∩ .Ioi x₀)).Tendsto f (nhds L)) :
-- imply
  RightLimitExists X f x₀ ∧ right_limit X f x₀ = L :=
-- proof
  Chapter9.right_limit.eq had h


-- created on 2026-10-22
