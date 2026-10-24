import Mathlib
import sympy.Basic
open Finset BigOperators


namespace BooleanFourier

/--
[noiseStability_mono](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/NoiseStabilityMono.lean)
-/
@[path]
lemma noiseStability_mono
  {n : ℕ}
  {ρ σ : ℝ}
  {f : (Fin n → Bool) → ℝ}
-- given
  (hρ₀ : 0 ≤ ρ)
  (hρσ : ρ ≤ σ) :
-- imply
  noiseStability ρ f ≤ noiseStability σ f := by
-- proof
  rw [noiseStability_eq_sum, noiseStability_eq_sum]
  apply Finset.sum_le_sum
  intro S _
  apply mul_le_mul_of_nonneg_right
  · exact pow_le_pow_left₀ hρ₀ hρσ S.card
  · exact sq_nonneg _

end BooleanFourier

namespace BooleanFourier

/--
[noiseStability_at_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/NoiseStabilityMono.lean)
-/
@[path]
lemma noiseStability_at_zero
  {n : ℕ}
  {f : (Fin n → Bool) → ℝ} :
-- imply
  noiseStability 0 f = fourierCoeff f ∅ ^ 2 :=
-- proof
  noiseStability_zero f

end BooleanFourier

namespace BooleanFourier

/--
[noiseStability_at_one_of_boolean](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/NoiseStabilityMono.lean)
-/
@[path]
lemma noiseStability_at_one_of_boolean
  {n : ℕ}
  {f : (Fin n → Bool) → Bool} :
-- imply
  noiseStability 1 (fun x => boolToReal (f x)) = 1 := by
-- proof
  rw [noiseStability_one]
  exact parseval_signed f

end BooleanFourier

namespace BooleanFourier

/--
[noiseStability_bounds_of_boolean](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/NoiseStabilityMono.lean)
-/
@[path]
lemma noiseStability_bounds_of_boolean
  {n : ℕ}
  {ρ : ℝ}
  {f : (Fin n → Bool) → Bool}
-- given
  (hρ₀ : 0 ≤ ρ)
  (hρ₁ : ρ ≤ 1) :
-- imply
  fourierCoeff (fun x => boolToReal (f x)) ∅ ^ 2 ≤ noiseStability ρ (fun x => boolToReal (f x)) ∧ noiseStability ρ (fun x => boolToReal (f x)) ≤ 1 :=
-- proof
  noiseStability_bounds_boolean ρ hρ₀ hρ₁ f

end BooleanFourier


-- created on 2026-10-23
