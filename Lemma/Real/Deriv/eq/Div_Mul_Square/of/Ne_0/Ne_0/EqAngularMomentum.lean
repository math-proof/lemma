import sympy.physics.vector.kinematics
import sympy.Basic


/--
From \(J=m\rho^2\dot\theta\): \(\dot\theta=J/(m\rho^2)\).
-/
@[main]
private lemma main
  {m J : ℝ}
  {ρ θ : ℝ → ℝ}
  {t : ℝ}
-- given
  (hm : m ≠ 0)
  (hρ : ρ t ≠ 0)
  (hJ : angular_momentum m ρ θ t = J) :
-- imply
  deriv θ t = J / (m * (ρ t) ^ 2) := by
-- proof
  have h : m * ((ρ t) ^ 2 * deriv θ t) = J := by
    simpa [angular_momentum, specific_angular_momentum] using hJ
  have hρ2 : (ρ t) ^ 2 ≠ 0 := pow_ne_zero 2 hρ
  field_simp [hm, hρ2] at h ⊢
  linarith


-- created on 2026-09-29
