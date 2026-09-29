import Mathlib.Analysis.Calculus.Deriv.Basic
import Lemma.Real.Velocity.eq.AddSMulSMul.of.DifferentiableAt.DifferentiableAt
import sympy.physics.vector.kinematics
import sympy.Basic


/--
Uniform circular motion (notes §11): if \(\rho\equiv\rho_0\) and \(\dot\theta\equiv\omega\), then
\(\vec{v}=\rho_0\omega\,\hat{\theta}\).
-/
@[main]
private lemma main
  {ρ θ : ℝ → ℝ}
  {ρ₀ ω t : ℝ}
-- given
  (hρ : ρ = fun _ => ρ₀)
  (hθ : DifferentiableAt ℝ θ t)
  (hω : deriv θ = fun _ => ω) :
-- imply
  velocity (polar_position ρ θ) t = (ρ₀ * ω) • polar_angular (θ t) := by
-- proof
  subst hρ
  have hv := Real.Velocity.eq.AddSMulSMul.of.DifferentiableAt.DifferentiableAt
    (differentiableAt_const (ρ₀ : ℝ)) hθ
  rw [hv, hω, deriv_const]
  simp [smul_smul]


-- created on 2026-09-28
