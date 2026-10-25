import Mathlib
import sympy.Basic
import Abbrev.Analysis.Section_9_5.Part2
open Chapter9
open Chapter9.right_limit


/--
[right_limit.conv](https://github.com/teorth/analysis/blob/main/Analysis/Section_9_5.lean)
-/
@[path]
private lemma main
  {X: Set ℝ}
  {f: ℝ → ℝ}
  {x₀:ℝ}
  {a:ℕ → ℝ}
-- given
  (had: AdherentPt x₀ (X ∩ .Ioi x₀))
  (h: RightLimitExists X f x₀)
  (ha: ∀ n, a n ∈ X ∩ .Ioi x₀)
  (hconv: Filter.atTop.Tendsto a (nhds x₀)) :
-- imply
  Filter.atTop.Tendsto (fun n ↦ f (a n)) (nhds (right_limit X f x₀)) :=
-- proof
  Chapter9.right_limit.conv had h a ha hconv


-- created on 2026-10-22
