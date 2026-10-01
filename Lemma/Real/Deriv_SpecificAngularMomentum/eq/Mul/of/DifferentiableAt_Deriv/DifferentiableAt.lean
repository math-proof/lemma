import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import sympy.physics.vector.kinematics
import sympy.Basic


/--
Identity for the derivative of specific angular momentum
\(h=\rho^2\dot\theta\):
\(\dot h=\rho(\rho\ddot\theta+2\dot\rho\dot\theta)\).
-/
@[main]
private lemma main
  {ρ θ : ℝ → ℝ}
  {t : ℝ}
-- given
  (hρ : DifferentiableAt ℝ ρ t)
  (hθ' : DifferentiableAt ℝ (deriv θ) t) :
-- imply
  deriv (specific_angular_momentum ρ θ) t =
    ρ t * (ρ t * deriv (deriv θ) t + 2 * deriv ρ t * deriv θ t) := by
-- proof
  unfold specific_angular_momentum
  rw [show (fun t => (ρ t) ^ 2 * deriv θ t) = (ρ * ρ) * deriv θ by
    ext s; simp [pow_two, Pi.mul_apply]]
  have h := (hρ.hasDerivAt.mul hρ.hasDerivAt).mul hθ'.hasDerivAt
  rw [h.deriv]
  simp [Pi.mul_apply]
  ring


-- created on 2026-09-28
