import Mathlib.Analysis.Calculus.MeanValue
import Lemma.Real.Deriv_SpecificAngularMomentum.eq.Zero.of.Eq_0.DifferentiableAt_Deriv.DifferentiableAt
import sympy.physics.vector.kinematics
import sympy.Basic


/--
If the transverse acceleration coefficient vanishes everywhere, then
specific angular momentum \(\rho^2\dot\theta\) is constant.
-/
@[path]
private lemma main
  {ρ θ : ℝ → ℝ}
-- given
  (hρ : Differentiable ℝ ρ)
  (hθ' : Differentiable ℝ (deriv θ))
  (h : ∀ t, ρ t * deriv (deriv θ) t + 2 * deriv ρ t * deriv θ t = 0) :
-- imply
  ∃ C, ∀ t, specific_angular_momentum ρ θ t = C := by
-- proof
  have hfun : specific_angular_momentum ρ θ = (ρ * ρ) * deriv θ := by
    ext s
    simp [specific_angular_momentum, pow_two, Pi.mul_apply]
  refine ⟨specific_angular_momentum ρ θ 0, fun t => ?_⟩
  refine is_const_of_deriv_eq_zero ?_ ?_ t 0
  · rw [hfun]
    intro s
    exact ((hρ s).mul (hρ s)).mul (hθ' s)
  · intro s
    exact Real.Deriv_SpecificAngularMomentum.eq.Zero.of.Eq_0.DifferentiableAt_Deriv.DifferentiableAt
      (hρ s) (hθ' s) (h s)


-- created on 2026-09-28
