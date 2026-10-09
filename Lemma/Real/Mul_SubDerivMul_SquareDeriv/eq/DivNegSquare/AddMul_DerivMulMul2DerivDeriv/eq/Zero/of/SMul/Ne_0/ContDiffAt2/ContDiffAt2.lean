import Mathlib.Analysis.Calculus.ContDiff.Basic
import Lemma.Real.Acceleration.eq.AddSMulS.of.ContDiffAt2.ContDiffAt2
import Lemma.Real.EqAndEq_0.of.AddSMulS.eq.SMul
import sympy.physics.vector.kinematics
import sympy.Basic


/--
Inverse-square force in polar components (notes §12):
\(m\vec{a}=-(C/\rho^2)\hat{r}\) implies the radial ODE and vanishing transverse coefficient.
-/
@[path]
private lemma main
  {ρ θ : ℝ → ℝ}
  {m C t : ℝ}
-- given
  (hρ : ContDiffAt ℝ 2 ρ t)
  (hθ : ContDiffAt ℝ 2 θ t)
  (hm : m ≠ 0)
  (hne : ρ t ≠ 0)
  (hF : m • acceleration (polar_position ρ θ) t = -(C / (ρ t) ^ 2) • polar_radial (θ t)) :
-- imply
  m * (deriv (deriv ρ) t - ρ t * (deriv θ t) ^ 2) = -C / (ρ t) ^ 2 ∧
    ρ t * deriv (deriv θ) t + 2 * deriv ρ t * deriv θ t = 0 := by
-- proof
  have _ := hne
  have ha := Real.Acceleration.eq.AddSMulS.of.ContDiffAt2.ContDiffAt2 hρ hθ
  rw [ha, smul_add, smul_smul, smul_smul, (neg_div (ρ t ^ 2) C).symm] at hF
  have hbasis :=
    Real.EqAndEq_0.of.AddSMulS.eq.SMul (θ := θ t)
      (a := m * (deriv (deriv ρ) t - ρ t * (deriv θ t) ^ 2))
      (b := m * (ρ t * deriv (deriv θ) t + 2 * deriv ρ t * deriv θ t))
      (c := -C / (ρ t) ^ 2) hF
  exact ⟨hbasis.1, (mul_eq_zero.mp hbasis.2).resolve_left hm⟩


-- created on 2026-09-28
