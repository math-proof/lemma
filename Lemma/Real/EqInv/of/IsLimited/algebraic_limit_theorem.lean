import Mathlib.Topology.Algebra.GroupWithZero
import sympy.series.limits
import sympy.Basic


@[path]
private lemma main
  {f : ℝ → ℝ}
  {x₀ A : ℝ}
-- given
  (h₀ : lim [x → x₀] f x = A)
  (h₁ : A ≠ 0) :
-- imply
  lim [x → x₀] (f x)⁻¹ = A⁻¹ := by
-- proof
  apply h₀.inv₀ h₁


-- created on 2020-06-18
-- updated on 2026-10-17
