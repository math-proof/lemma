import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Lemma.Real.HasDerivAt_PolarAngular_SMulNegPolarRadial.of.DifferentiableAt
import Lemma.Real.HasDerivAt_PolarRadial_SMulDeriv_PolarAngular.of.DifferentiableAt
import Lemma.Real.Velocity.eq.AddSMulSMul.of.DifferentiableAt.DifferentiableAt
import sympy.physics.vector.kinematics
import sympy.Basic


/--
Polar acceleration (notes §10):
\(\vec{a}=(\ddot\rho-\rho\dot\theta^2)\hat{r}+(\rho\ddot\theta+2\dot\rho\dot\theta)\hat{\theta}\).
-/
@[path]
private lemma main
  {ρ θ : ℝ → ℝ}
  {t : ℝ}
-- given
  (hρ : ContDiffAt ℝ 2 ρ t)
  (hθ : ContDiffAt ℝ 2 θ t) :
-- imply
  acceleration (polar_position ρ θ) t =
    (deriv (deriv ρ) t - ρ t * (deriv θ t) ^ 2) • polar_radial (θ t) +
      (ρ t * deriv (deriv θ) t + 2 * deriv ρ t * deriv θ t) • polar_angular (θ t) := by
-- proof
  have hρ1 : DifferentiableAt ℝ ρ t := hρ.differentiableAt (by decide)
  have hθ1 : DifferentiableAt ℝ θ t := hθ.differentiableAt (by decide)
  have hρ' : DifferentiableAt ℝ (deriv ρ) t :=
    (hρ.derivWithin (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt (by decide)
  have hθ' : DifferentiableAt ℝ (deriv θ) t :=
    (hθ.derivWithin (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt (by decide)
  have hne : (2 : WithTop ℕ∞) ≠ ((⊤ : ℕ∞) : WithTop ℕ∞) := by decide
  let V : ℝ → EuclideanVec 2 :=
    (fun s => deriv ρ s • (polar_radial ∘ θ) s) +
      fun s => (ρ s * deriv θ s) • (polar_angular ∘ θ) s
  have hV_eq : velocity (polar_position ρ θ) =ᶠ[nhds t] V := by
    filter_upwards [hρ.eventually hne, hθ.eventually hne] with s hsρ hsθ
    have hv := Real.Velocity.eq.AddSMulSMul.of.DifferentiableAt.DifferentiableAt
      (hsρ.differentiableAt (by decide)) (hsθ.differentiableAt (by decide))
    simpa [V, Pi.add_apply, Function.comp_def, smul_smul] using hv
  have hr := Real.HasDerivAt_PolarRadial_SMulDeriv_PolarAngular.of.DifferentiableAt hθ1
  have ha := Real.HasDerivAt_PolarAngular_SMulNegPolarRadial.of.DifferentiableAt hθ1
  have h1 := hρ'.hasDerivAt.smul hr
  have h2 := (hρ1.hasDerivAt.mul hθ'.hasDerivAt).smul ha
  have hacc := (h1.add h2).congr_of_eventuallyEq hV_eq
  simp only [acceleration]
  rw [hacc.deriv]
  simp only [Function.comp_def, Pi.mul_apply, smul_smul, smul_neg, neg_smul]
  module


-- created on 2026-09-28
