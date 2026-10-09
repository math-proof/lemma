import Mathlib.Analysis.Calculus.Deriv.Basic
import Lemma.Real.Inner_PolarRadial_PolarAngular.eq.Zero
import Lemma.Real.NormPolarAngular.eq.One
import Lemma.Real.NormPolarRadial.eq.One
import Lemma.Real.Velocity.eq.AddSMulSMul.of.DifferentiableAt.DifferentiableAt
import sympy.physics.vector.kinematics
import sympy.Basic


/--
Polar speed squared: \(v^2=\dot\rho^2+\rho^2\dot\theta^2\).
-/
@[path]
private lemma main
  {ρ θ : ℝ → ℝ}
  {t : ℝ}
-- given
  (hρ : DifferentiableAt ℝ ρ t)
  (hθ : DifferentiableAt ℝ θ t) :
-- imply
  ‖velocity (polar_position ρ θ) t‖ ^ 2 =
    (deriv ρ t) ^ 2 + (ρ t) ^ 2 * (deriv θ t) ^ 2 := by
-- proof
  have hv := Real.Velocity.eq.AddSMulSMul.of.DifferentiableAt.DifferentiableAt hρ hθ
  rw [hv]
  set a := deriv ρ t
  set b := ρ t * deriv θ t
  have hform :
      a • polar_radial (θ t) + ρ t • (deriv θ t • polar_angular (θ t)) =
        a • polar_radial (θ t) + b • polar_angular (θ t) := by
    simp [b, smul_smul]
  rw [hform]
  set ur := polar_radial (θ t)
  set ua := polar_angular (θ t)
  have hr1 : ‖ur‖ = (1 : ℝ) := Real.NormPolarRadial.eq.One (θ t)
  have hθ1 : ‖ua‖ = (1 : ℝ) := Real.NormPolarAngular.eq.One (θ t)
  have horth : inner (𝕜 := ℝ) ur ua = 0 :=
    Real.Inner_PolarRadial_PolarAngular.eq.Zero (θ t)
  have hnorm_a : ‖a • ur‖ ^ 2 = a ^ 2 := by
    rw [norm_smul, hr1, mul_one, Real.norm_eq_abs, sq_abs]
  have hnorm_b : ‖b • ua‖ ^ 2 = b ^ 2 := by
    rw [norm_smul, hθ1, mul_one, Real.norm_eq_abs, sq_abs]
  have hinner : inner (𝕜 := ℝ) (a • ur) (b • ua) = 0 := by
    rw [real_inner_smul_left, real_inner_smul_right, horth, mul_zero, mul_zero]
  have hexpand :
      ‖a • ur + b • ua‖ ^ 2 =
        ‖a • ur‖ ^ 2 + ‖b • ua‖ ^ 2 + 2 * inner (𝕜 := ℝ) (a • ur) (b • ua) := by
    have h1 := (real_inner_self_eq_norm_sq (a • ur + b • ua)).symm
    rw [h1]
    rw [inner_add_left, inner_add_right, inner_add_right]
    have hcomm := real_inner_comm (b • ua) (a • ur)
    rw [hcomm]
    simp only [real_inner_self_eq_norm_sq]
    ring
  rw [hexpand, hnorm_a, hnorm_b, hinner]
  simp [b]
  ring


-- created on 2026-09-29
