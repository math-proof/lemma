import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import sympy.dynamics.actor_critic
import sympy.Basic


@[main]
private lemma main
  {u : ℝ → ℝ}
  {a : ℝ → ℝ}
-- given
  (h₀ : ∀ t, 0 ≤ t → HasDerivWithinAt u (-(a t * u t)) (Set.Ici t) t)
  (h₁ : Continuous u)
  (h₂ : Continuous a) :
-- imply
  ∀ t, 0 ≤ t → u t * scalar_integrating_factor a t = u 0 := by
-- proof
  intro T hT
  have hI : ∀ t, HasDerivAt (fun x => ∫ s in (0 : ℝ)..x, a s) (a t) t := fun t => (h₂.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hE : ∀ t, HasDerivAt (scalar_integrating_factor a) (scalar_integrating_factor a t * a t) t := fun t => (Real.hasDerivAt_exp _).comp t (hI t)
  have hcont : Continuous fun t => u t * scalar_integrating_factor a t := h₁.mul (continuous_iff_continuousAt.2 fun t => (hE t).continuousAt)
  have hzero : ∀ t ∈ Set.Ico 0 T, HasDerivWithinAt (fun t => u t * scalar_integrating_factor a t) 0 (Set.Ici t) t := by
    intro t ht
    have h := (h₀ t ht.1).mul (hE t).hasDerivWithinAt
    exact h.congr_deriv (by ring)
  have := constant_of_has_deriv_right_zero hcont.continuousOn hzero T ⟨hT, le_rfl⟩
  simpa [scalar_integrating_factor] using this


-- created on 2026-09-26
