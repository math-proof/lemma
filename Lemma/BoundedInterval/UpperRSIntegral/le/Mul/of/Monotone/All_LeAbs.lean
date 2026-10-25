import Mathlib
import sympy.Basic
import Abbrev.Analysis.Section_11_8.Part7
open Chapter11.BoundedInterval Chapter9
open Chapter11


/--
[RS_upper_integral_le](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_8.lean)
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
  upper_RS_integral f I α ≤ M * α[I]ₗ :=
-- proof
  Chapter11.RS_upper_integral_le h hα


-- created on 2026-10-22
