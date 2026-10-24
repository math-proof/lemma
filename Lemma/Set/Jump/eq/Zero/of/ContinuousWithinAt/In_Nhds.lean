import Mathlib
import sympy.Basic
import sympy.analysis.Section_11_8
open Chapter11.BoundedInterval Chapter9
open Chapter11


/--
[jump_of_continuous](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_8.lean)
-/
@[path]
private lemma main
  {X:Set ℝ}
  {f: ℝ → ℝ}
  {x₀:ℝ}
-- given
  (h : X ∈ nhds x₀)
  (hf: ContinuousWithinAt f X x₀) :
-- imply
  jump f x₀ = 0 :=
-- proof
  Chapter11.jump_of_continuous h hf


-- created on 2026-10-22
