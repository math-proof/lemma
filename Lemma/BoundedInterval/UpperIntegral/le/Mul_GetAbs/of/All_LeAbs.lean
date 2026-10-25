import Mathlib
import sympy.Basic
import Abbrev.Analysis.Section_11_3.Part5
open Chapter11.BoundedInterval Chapter9
open Chapter11


/--
[upper_integral_le](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_3.lean)
-/
@[path]
private lemma main
  {f:ℝ → ℝ}
  {I: BoundedInterval}
  {M:ℝ}
-- given
  (h: ∀ x ∈ (I:Set ℝ), |f x| ≤ M) :
-- imply
  upper_integral f I ≤ M * |I|ₗ :=
-- proof
  Chapter11.upper_integral_le h


-- created on 2026-10-22
