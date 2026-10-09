import Lemma.Real.ArealSpeed.eq.Div.of.Ne_0.EqAngularMomentum
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import sympy.physics.vector.kinematics
import sympy.Basic


/--
Kepler's second law integrated over one period \(T\):
\(S=\displaystyle\int_0^T \dfrac{J}{2m}\,dt=\dfrac{JT}{2m}\).
-/
@[path]
private lemma main
  {m J T : ℝ}
  {ρ θ : ℝ → ℝ}
-- given
  (hm : m ≠ 0)
  (hJ : ∀ t, angular_momentum m ρ θ t = J) :
-- imply
  ∫ t in (0 : ℝ)..T, areal_speed m ρ θ t = J * T / (2 * m) := by
-- proof
  have h : ∀ t, areal_speed m ρ θ t = J / (2 * m) := fun t =>
    Real.ArealSpeed.eq.Div.of.Ne_0.EqAngularMomentum hm (hJ t)
  simp only [h, intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  ring


-- created on 2026-09-29