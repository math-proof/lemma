import Mathlib
import sympy.Basic
import Abbrev.Analysis.Section_11_8.Part7
open Chapter11.BoundedInterval Chapter9
open Chapter11


/--
[jump_of_monotone](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_8.lean)
-/
@[path]
private lemma main
  {f: ℝ → ℝ}
  {x₀:ℝ}
-- given
  (hf: Monotone f) :
-- imply
  0 ≤ jump f x₀ :=
-- proof
  Chapter11.jump_of_monotone x₀ hf


-- created on 2026-10-22
