import Mathlib
import sympy.Basic
import sympy.analysis.Section_11_8
open Chapter11.BoundedInterval Chapter9
open Chapter11


/--
[right_lim_of_monotone'](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_8.lean)
-/
@[path]
private lemma main
  {f: ℝ → ℝ}
  {x₀:ℝ}
-- given
  (hf: Monotone f) :
-- imply
  right_lim f x₀ = sInf (f '' .Ioi x₀) :=
-- proof
  Chapter11.right_lim_of_monotone' x₀ hf


-- created on 2026-10-22
