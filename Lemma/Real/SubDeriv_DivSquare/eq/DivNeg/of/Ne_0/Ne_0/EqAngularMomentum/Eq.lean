import Lemma.Real.Deriv.eq.Div_Mul_Square.of.Ne_0.Ne_0.EqAngularMomentum
import sympy.physics.vector.kinematics
import sympy.Basic


/--
Substitute \(\dot\theta=J/(m\rho^2)\) into the radial force equation:
\(\ddot\rho-J^2/(m^2\rho^3)=-C/(m\rho^2)\).
-/
@[path]
private lemma main
  {m J C : ℝ}
  {ρ θ : ℝ → ℝ}
  {t : ℝ}
-- given
  (hm : m ≠ 0)
  (hρ : ρ t ≠ 0)
  (hJ : angular_momentum m ρ θ t = J)
  (hrad : m * (deriv (deriv ρ) t - ρ t * (deriv θ t) ^ 2) = -C / (ρ t) ^ 2) :
-- imply
  deriv (deriv ρ) t - J ^ 2 / (m ^ 2 * (ρ t) ^ 3) = -C / (m * (ρ t) ^ 2) := by
-- proof
  have hθ := Real.Deriv.eq.Div_Mul_Square.of.Ne_0.Ne_0.EqAngularMomentum hm hρ hJ
  rw [hθ] at hrad
  have hr2 : (ρ t) ^ 2 ≠ 0 := pow_ne_zero 2 hρ
  have hr3 : (ρ t) ^ 3 ≠ 0 := pow_ne_zero 3 hρ
  have hm2 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm
  field_simp [hm, hr2, hr3, hm2] at hrad ⊢
  linarith


-- created on 2026-09-29
