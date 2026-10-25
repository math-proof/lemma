import Mathlib
import sympy.Basic
import Def.v1.Atlas.BooleanFunctions.code.Theorems
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.Theorems
open Finset BigOperators


namespace BooleanFourier

/--
[noiseStability_ge_fourierCoeff_empty_sq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/NoiseStabilityBounds.lean)
-/
@[path]
lemma noiseStability_ge_fourierCoeff_empty_sq
  {n : ℕ}
  {ρ : ℝ}
  {f : (Fin n → Bool) → ℝ}
-- given
  (hρ₀ : 0 ≤ ρ) :
-- imply
  noiseStability ρ f ≥ fourierCoeff f ∅ ^ 2 := by
-- proof
  rw [noiseStability_eq_sum]
  have hterm : ∀ S : Finset (Fin n),
    0 ≤ ρ ^ S.card * fourierCoeff f S ^ 2 :=
    fun S => mul_nonneg (pow_nonneg hρ₀ _) (sq_nonneg _)
  calc ∑ S : Finset (Fin n), ρ ^ S.card * fourierCoeff f S ^ 2
    ≥ ρ ^ (∅ : Finset (Fin n)).card * fourierCoeff f ∅ ^ 2 :=
      Finset.single_le_sum (fun S _ => hterm S) (Finset.mem_univ ∅)
    _ = fourierCoeff f ∅ ^ 2 := by simp

end BooleanFourier

namespace BooleanFourier

/--
[noiseStability_le_sum_sq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/NoiseStabilityBounds.lean)
-/
@[path]
lemma noiseStability_le_sum_sq
  {n : ℕ}
  {ρ : ℝ}
  {f : (Fin n → Bool) → ℝ}
-- given
  (hρ₀ : 0 ≤ ρ)
  (hρ₁ : ρ ≤ 1) :
-- imply
  noiseStability ρ f ≤ ∑ S : Finset (Fin n), fourierCoeff f S ^ 2 := by
-- proof
  rw [noiseStability_eq_sum]
  apply Finset.sum_le_sum
  intro S _
  exact mul_le_of_le_one_left (sq_nonneg _) (pow_le_one₀ hρ₀ hρ₁)

end BooleanFourier

namespace BooleanFourier

/--
[noiseStability_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/NoiseStabilityBounds.lean)
-/
@[path]
lemma noiseStability_bounds
  {n : ℕ}
  {ρ : ℝ}
  {f : (Fin n → Bool) → ℝ}
-- given
  (hρ₀ : 0 ≤ ρ)
  (hρ₁ : ρ ≤ 1) :
-- imply
  fourierCoeff f ∅ ^ 2 ≤ noiseStability ρ f ∧ noiseStability ρ f ≤ ∑ S : Finset (Fin n), fourierCoeff f S ^ 2 :=
-- proof
  ⟨noiseStability_ge_fourierCoeff_empty_sq ρ hρ₀ f,
    noiseStability_le_sum_sq ρ hρ₀ hρ₁ f⟩

end BooleanFourier

namespace BooleanFourier

/--
[noiseStability_le_one_of_boolean](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/NoiseStabilityBounds.lean)
-/
@[path]
lemma noiseStability_le_one_of_boolean
  {n : ℕ}
  {ρ : ℝ}
  {f : (Fin n → Bool) → Bool}
-- given
  (hρ₀ : 0 ≤ ρ)
  (hρ₁ : ρ ≤ 1) :
-- imply
  noiseStability ρ (fun x => boolToReal (f x)) ≤ 1 := by
-- proof
  have h := noiseStability_le_sum_sq ρ hρ₀ hρ₁ (fun x => boolToReal (f x))
  linarith [parseval_signed f]

end BooleanFourier

namespace BooleanFourier

/--
[noiseStability_bounds_boolean](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/NoiseStabilityBounds.lean)
-/
@[path]
lemma noiseStability_bounds_boolean
  {n : ℕ}
  {ρ : ℝ}
  {f : (Fin n → Bool) → Bool}
-- given
  (hρ₀ : 0 ≤ ρ)
  (hρ₁ : ρ ≤ 1) :
-- imply
  fourierCoeff (fun x => boolToReal (f x)) ∅ ^ 2 ≤ noiseStability ρ (fun x => boolToReal (f x)) ∧ noiseStability ρ (fun x => boolToReal (f x)) ≤ 1 :=
-- proof
  ⟨noiseStability_ge_fourierCoeff_empty_sq ρ hρ₀ _,
    noiseStability_le_one_of_boolean ρ hρ₀ hρ₁ f⟩

end BooleanFourier


-- created on 2026-10-23
