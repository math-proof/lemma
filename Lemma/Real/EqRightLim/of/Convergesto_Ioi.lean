import Mathlib
import sympy.Basic
import sympy.analysis.Section_11_8
open Chapter11.BoundedInterval Chapter9
open Chapter11


/--
[right_lim_def](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_8.lean)
-/
@[path]
private lemma main
  {f: ℝ → ℝ}
  {x₀ L:ℝ}
-- given
  (h: Convergesto (.Ioi x₀) f L x₀) :
-- imply
  right_lim f x₀ = L :=
-- proof
  Chapter11.right_lim_def h


-- created on 2026-10-22
