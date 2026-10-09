import Lemma.Real.Deriv_SpecificAngularMomentum.eq.Mul.of.DifferentiableAt_Deriv.DifferentiableAt
import sympy.physics.vector.kinematics
import sympy.Basic


/--
Vanishing transverse acceleration coefficient implies
\(\dfrac{d}{dt}(\rho^2\dot\theta)=0\) at \(t\).
-/
@[path]
private lemma main
  {ρ θ : ℝ → ℝ}
  {t : ℝ}
-- given
  (hρ : DifferentiableAt ℝ ρ t)
  (hθ' : DifferentiableAt ℝ (deriv θ) t)
  (h : ρ t * deriv (deriv θ) t + 2 * deriv ρ t * deriv θ t = 0) :
-- imply
  deriv (specific_angular_momentum ρ θ) t = 0 := by
-- proof
  rw [Real.Deriv_SpecificAngularMomentum.eq.Mul.of.DifferentiableAt_Deriv.DifferentiableAt hρ hθ', h]
  ring


-- created on 2026-09-28
