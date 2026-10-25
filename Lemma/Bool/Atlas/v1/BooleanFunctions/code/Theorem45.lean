import Mathlib
import sympy.Basic
import Def.v1.Atlas.BooleanFunctions.code.NoiseSensitivity
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.NoiseSensitivity
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.InfluenceFourier
import Def.v1.Atlas.BooleanFunctions.code.InfluenceFourier
open Finset BigOperators


namespace BooleanFourier

/--
[one_sub_pow_le_mul_card](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Theorem45.lean)
-/
@[path]
lemma one_sub_pow_le_mul_card
  {t : ℝ}
  {k : ℕ}
-- given
  (ht₀ : 0 ≤ t)
  (ht₁ : t ≤ 1) :
-- imply
  1 - (1 - t) ^ k ≤ t * k := by
-- proof
  induction k with
  | zero => simp
  | succ k ih =>
    have h1t : 0 ≤ 1 - t := by linarith
    have h1t' : 1 - t ≤ 1 := by linarith
    calc 1 - (1 - t) ^ (k + 1)
      = 1 - (1 - t) ^ k * (1 - t) := by ring_nf
      _ = (1 - (1 - t) ^ k) + (1 - t) ^ k * t := by ring
      _ ≤ t * k + (1 - t) ^ k * t := by linarith
      _ ≤ t * k + 1 * t := by
        have : (1 - t) ^ k ≤ 1 := pow_le_one₀ h1t h1t'
        nlinarith
      _ = t * (k + 1) := by ring
      _ = t * ↑(k + 1) := by push_cast; ring

end BooleanFourier

namespace BooleanFourier

/--
[noiseSensitivity_le_delta_mul_totalInfluenceReal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Theorem45.lean)
-/
@[path]
lemma noiseSensitivity_le_delta_mul_totalInfluenceReal
  {n : ℕ}
  {δ : ℝ}
  {f : (Fin n → Bool) → ℝ}
-- given
  (hδ₀ : 0 ≤ δ)
  (hδ₁ : δ ≤ 1 / 2) :
-- imply
  (1 / 2 * ∑ S : Finset (Fin n), (1 - (1 - 2 * δ) ^ S.card) * fourierCoeff f S ^ 2) ≤ δ * totalInfluenceReal f := by
-- proof
  rw [totalInfluenceReal_eq_sum_card_fourierCoeff_sq]
  have h2δ_bound : 2 * δ ≤ 1 := by linarith
  have h2δ_nonneg : 0 ≤ 2 * δ := by linarith
  suffices h : ∀ S : Finset (Fin n),
    1 / 2 * ((1 - (1 - 2 * δ) ^ S.card) * fourierCoeff f S ^ 2) ≤
    δ * ((S.card : ℝ) * fourierCoeff f S ^ 2) by
    calc 1 / 2 * ∑ S : Finset (Fin n),
      (1 - (1 - 2 * δ) ^ S.card) * fourierCoeff f S ^ 2
      = ∑ S : Finset (Fin n),
        1 / 2 * ((1 - (1 - 2 * δ) ^ S.card) * fourierCoeff f S ^ 2) := by
        rw [Finset.mul_sum]
      _ ≤ ∑ S : Finset (Fin n),
        δ * ((S.card : ℝ) * fourierCoeff f S ^ 2) :=
        Finset.sum_le_sum (fun S _ => h S)
      _ = δ * ∑ S : Finset (Fin n), (S.card : ℝ) * fourierCoeff f S ^ 2 := by
        rw [← Finset.mul_sum]
  intro S
  have hfc_sq : 0 ≤ fourierCoeff f S ^ 2 := sq_nonneg _
  have hbern : 1 - (1 - 2 * δ) ^ S.card ≤ 2 * δ * S.card :=
    one_sub_pow_le_mul_card (2 * δ) h2δ_nonneg h2δ_bound S.card
  calc 1 / 2 * ((1 - (1 - 2 * δ) ^ S.card) * fourierCoeff f S ^ 2)
    ≤ 1 / 2 * (2 * δ * ↑S.card * fourierCoeff f S ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1 / 2)
      exact mul_le_mul_of_nonneg_right hbern hfc_sq
    _ = δ * (↑S.card * fourierCoeff f S ^ 2) := by ring

end BooleanFourier

namespace BooleanFourier

/--
[noiseSensitivity_le_delta_mul_totalInfluence](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Theorem45.lean)
-/
@[path]
lemma noiseSensitivity_le_delta_mul_totalInfluence
  {n : ℕ}
  {δ : ℝ}
  {f : (Fin n → Bool) → Bool}
-- given
  (hδ₀ : 0 ≤ δ)
  (hδ₁ : δ ≤ 1 / 2) :
-- imply
  noiseSensitivity δ f ≤ δ * totalInfluenceReal (fun x => boolToReal (f x)) := by
-- proof
  rw [noiseSensitivity_eq_fourier_sum]
  exact noiseSensitivity_le_delta_mul_totalInfluenceReal δ hδ₀ hδ₁ _

end BooleanFourier


-- created on 2026-10-23
