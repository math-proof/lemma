import Lemma.Real.SquareNormVelocity.eq.AddSquareS.of.DifferentiableAt.DifferentiableAt
import sympy.physics.vector.kinematics
import sympy.Basic


/--
Mechanical energy in polar coordinates:
\(E=\frac12 m(\dot\rho^2+\rho^2\dot\theta^2)+C/\rho\).
-/
@[path]
private lemma main
  {m C : ℝ}
  {ρ θ : ℝ → ℝ}
  {t : ℝ}
-- given
  (hρ : DifferentiableAt ℝ ρ t)
  (hθ : DifferentiableAt ℝ θ t) :
-- imply
  mechanical_energy m C ρ θ t =
    (1 / 2) * m * ((deriv ρ t) ^ 2 + (ρ t) ^ 2 * (deriv θ t) ^ 2) + C / ρ t := by
-- proof
  have hv := Real.SquareNormVelocity.eq.AddSquareS.of.DifferentiableAt.DifferentiableAt hρ hθ
  simp only [mechanical_energy, hv]


-- created on 2026-09-29
