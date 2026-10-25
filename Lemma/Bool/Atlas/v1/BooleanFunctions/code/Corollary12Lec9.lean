import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.BooleanFunctions.code.Corollary12Lec9
open Finset BigOperators MeasureTheory ProbabilityTheory BooleanFourier


namespace BooleanFourier

/--
[isBooleanValued_hasBoundedRange](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Corollary12Lec9.lean)
-/
@[path]
lemma isBooleanValued_hasBoundedRange
  {n : ℕ}
  {f : (Fin n → Bool) → ℝ}
-- given
  (hf : IsBooleanValued f) :
-- imply
  HasBoundedRange f := by
-- proof
  intro x
  obtain h | h <;> rw [h] <;> constructor <;> norm_num := hf x

end BooleanFourier

namespace BooleanFourier

/--
[majority_is_stablest_boolean](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Corollary12Lec9.lean)
-/
@[path]
lemma majority_is_stablest_boolean
  {ρ : ℝ}
  {ε : ℝ}
-- given
  (hρ₀ : 0 ≤ ρ)
  (hρ₁ : ρ < 1)
  (hε : 0 < ε) :
-- imply
  ∃ δ > 0, ∀ (n : ℕ) (f : (Fin n → Bool) → ℝ), IsBooleanValued f → maxInfluence f ≤ δ → noiseStability ρ f ≤ halfspaceNoiseStability ρ (boolExpectation f) + ε := by
-- proof
  obtain ⟨δ, hδ_pos, hδ⟩ := majority_is_stablest_general ρ hρ₀ hρ₁ ε hε
  exact ⟨δ, hδ_pos, fun n f hBool hInf =>
    hδ n f (isBooleanValued_hasBoundedRange hBool) hInf⟩
end BooleanFourier



-- created on 2026-10-23
