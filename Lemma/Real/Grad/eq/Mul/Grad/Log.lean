import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import sympy.Basic
open Real


@[path]
private lemma main
  {f : ℝ → ℝ}
  {x : ℝ}
-- given
  (h₀ : DifferentiableAt ℝ f x)
  (h₁ : f x ≠ 0) :
-- imply
  deriv f x = f x * deriv (fun y => log (f y)) x := by
-- proof
  rw [deriv.log h₀ h₁]
  field_simp [h₁]


-- created on 2026-10-03
