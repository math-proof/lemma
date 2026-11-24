module
public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Def.v1.Atlas.BooleanFunctions.code.Stability
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.Stability
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.NoiseStability
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.NoiseStabilityBounds
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.Theorems
open Finset BigOperators


public section

namespace BooleanFourier

/--
[noiseStability_mono](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/NoiseStabilityMono.lean)
-/
@[path]
theorem noiseStability_mono
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
theorem noiseStability_at_zero
  {n : ℕ}
  {f : (Fin n → Bool) → ℝ} :
-- imply
  noiseStability 0 f = fourierCoeff f ∅ ^ 2 :=
-- proof
  noiseStability_zero

end BooleanFourier

namespace BooleanFourier

/--
[noiseStability_at_one_of_boolean](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/NoiseStabilityMono.lean)
-/
@[path]
theorem noiseStability_at_one_of_boolean
  {n : ℕ}
  {f : (Fin n → Bool) → Bool} :
-- imply
  noiseStability 1 (fun x => boolToReal (f x)) = 1 := by
-- proof
  rw [noiseStability_one]
  exact parseval_signed

end BooleanFourier

namespace BooleanFourier

/--
[noiseStability_bounds_of_boolean](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/NoiseStabilityMono.lean)
-/
@[path]
theorem noiseStability_bounds_of_boolean
  {n : ℕ}
  {ρ : ℝ}
  {f : (Fin n → Bool) → Bool}
-- given
  (hρ₀ : 0 ≤ ρ)
  (hρ₁ : ρ ≤ 1) :
-- imply
  fourierCoeff (fun x => boolToReal (f x)) ∅ ^ 2 ≤ noiseStability ρ (fun x => boolToReal (f x)) ∧ noiseStability ρ (fun x => boolToReal (f x)) ≤ 1 :=
-- proof
  noiseStability_bounds_boolean hρ₀ hρ₁

end BooleanFourier


-- created on 2026-10-23
-- updated on 2026-10-27
