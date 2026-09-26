import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import sympy.dynamics.actor_critic
import sympy.Basic
import Lemma.Real.All_EqMul_ScalarIntegratingFactor.of.Continuous.Continuous.All_HasDerivWithinAt


@[main]
private lemma main
  {d : ℕ}
  {r : ℝ}
  {θ : ℝ → EuclideanVec d}
  {h : ℝ → EuclideanVec d}
-- given
  (h₀ : ForwardSolvesActorBoxEquation r θ h)
  (h₁ : θ 0 ∈ actor_box d r) :
-- imply
  ∀ t, 0 ≤ t → θ t ∈ actor_box d r := by
-- proof
  intro t ht j
  obtain ⟨hl, hu⟩ := abs_le.1 (h₁ j)
  have hU := Real.All_EqMul_ScalarIntegratingFactor.of.Continuous.Continuous.All_HasDerivWithinAt (u := fun s => r - θ s j) (a := fun s => (r + θ s j) * h s j)
    (fun s hs => by
      exact HasDerivWithinAt.congr_deriv ((h₀.hasDeriv s j hs).const_sub r) (by ring)) (continuous_const.sub (h₀.cont_theta j)) ((continuous_const.add (h₀.cont_theta j)).mul (h₀.cont_h j)) t ht
  have hL := Real.All_EqMul_ScalarIntegratingFactor.of.Continuous.Continuous.All_HasDerivWithinAt (u := fun s => r + θ s j) (a := fun s => -((r - θ s j) * h s j))
    (fun s hs => by
      exact HasDerivWithinAt.congr_deriv ((h₀.hasDeriv s j hs).const_add r) (by ring)) (continuous_const.add (h₀.cont_theta j)) (((continuous_const.sub (h₀.cont_theta j)).mul (h₀.cont_h j)).neg) t ht
  have hpU := Real.exp_pos (∫ s in (0 : ℝ)..t, (r + θ s j) * h s j)
  have hpL := Real.exp_pos (∫ s in (0 : ℝ)..t, -((r - θ s j) * h s j))
  simp only [scalar_integrating_factor] at hU hL
  rw [abs_le]
  constructor
  · nlinarith
  · nlinarith


-- created on 2026-09-26
