import Mathlib
import sympy.Basic
import sympy.analysis.Section_11_8
open Chapter11.BoundedInterval Chapter9
open Chapter11


/--
[le_lower_RS_integral](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_8.lean)
-/
@[path]
private lemma main
  {f:ℝ → ℝ}
  {I: BoundedInterval}
  {M:ℝ}
  {α:ℝ → ℝ}
-- given
  (h: ∀ x ∈ (I:Set ℝ), |f x| ≤ M)
  (hα: Monotone α) :
-- imply
  -M * α[I]ₗ ≤ lower_RS_integral f I α :=
-- proof
  Chapter11.le_lower_RS_integral h hα


-- created on 2026-10-22
