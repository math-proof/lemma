import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Lemma.Real.Acceleration.eq.AddSMulS.of.ContDiffAt2.ContDiffAt2
import sympy.physics.vector.kinematics
import sympy.Basic


/--
Uniform circular motion (notes §11): if \(\rho\equiv\rho_0\) and \(\dot\theta\equiv\omega\), then
\(\vec{a}=-\rho_0\omega^2\,\hat{r}\).
-/
@[main]
private lemma main
  {ρ θ : ℝ → ℝ}
  {ρ₀ ω t : ℝ}
-- given
  (hρ : ρ = fun _ => ρ₀)
  (hθ : ContDiffAt ℝ 2 θ t)
  (hω : deriv θ = fun _ => ω) :
-- imply
  acceleration (polar_position ρ θ) t = -(ρ₀ * ω ^ 2) • polar_radial (θ t) := by
-- proof
  subst hρ
  have hρc : ContDiffAt ℝ 2 (fun _ : ℝ => ρ₀) t := contDiffAt_const
  have ha := Real.Acceleration.eq.AddSMulS.of.ContDiffAt2.ContDiffAt2 hρc hθ
  rw [ha, hω, deriv_const]
  simp [deriv_const, zero_mul, zero_smul, sub_eq_add_neg]


-- created on 2026-09-28
