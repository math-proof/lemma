import Mathlib
import sympy.Basic
import Def.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM6.HeatSymmetryEnergy
open MeasureTheory Real Filter Set CM6
open scoped ENNReal


namespace CM6

/--
[heat_translation_invariance](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM6/HeatSymmetryEnergy.lean)
-/
@[path]
lemma heat_translation_invariance
  {n : ℕ}
  {D A t₀ : ℝ}
  {x₀ : Fin n → ℝ}
  {u_t Δu : ℝ → (Fin n → ℝ) → ℝ}
-- given
  (hpde : ∀ t x, u_t t x - D * Δu t x = 0) :
-- imply
  ∀ t x, A * u_t (t - t₀) (x - x₀) - D * (A * Δu (t - t₀) (x - x₀)) = 0 := by
-- proof
  intro t x
  have h := hpde (t - t₀) (x - x₀)
  linear_combination A * h

end CM6


-- created on 2026-10-23
