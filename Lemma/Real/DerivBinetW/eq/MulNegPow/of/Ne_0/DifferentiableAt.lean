import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import sympy.physics.vector.kinematics
import sympy.Basic


/--
Binet first derivative: \(w'=-r^{-2}r'\) for \(w=1/r\).
-/
@[path]
private lemma main
  {r : ℝ → ℝ}
  {φ : ℝ}
-- given
  (hr0 : r φ ≠ 0)
  (hr : DifferentiableAt ℝ r φ) :
-- imply
  deriv (binet_w r) φ = -deriv r φ / (r φ) ^ 2 := by
-- proof
  have heq : binet_w r = fun ψ => (r ψ)⁻¹ := rfl
  rw [heq]
  exact (hr.hasDerivAt.inv hr0).deriv


-- created on 2026-09-29
