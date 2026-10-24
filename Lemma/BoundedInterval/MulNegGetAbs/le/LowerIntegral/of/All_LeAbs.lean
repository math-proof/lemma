import Mathlib
import sympy.Basic
import sympy.analysis.Section_11_3
open Chapter11.BoundedInterval Chapter9
open Chapter11


/--
[le_lower_integral](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_3.lean)
-/
@[path]
private lemma main
  {f:ℝ → ℝ}
  {I: BoundedInterval}
  {M:ℝ}
-- given
  (h: ∀ x ∈ (I:Set ℝ), |f x| ≤ M) :
-- imply
  -M * |I|ₗ ≤ lower_integral f I :=
-- proof
  Chapter11.le_lower_integral h


-- created on 2026-10-22
