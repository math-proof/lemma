import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.BooleanFunctions.code.DisagreementStability
open Finset BigOperators BooleanFourier


namespace BooleanFourier

/--
[disagreementProb_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/DisagreementStability.lean)
-/
@[path]
lemma disagreementProb_eq
  {n : ℕ}
  {ρ : ℝ}
  {f : (Fin n → Bool) → ℝ} :
-- imply
  disagreementProb ρ f = (1 - noiseStability ρ f) / 2 := by
-- proof
  simp only [disagreementProb, noiseStability]
  have h2n_pos : (0 : ℝ) < (2 : ℝ) ^ n := pow_pos (by norm_num : (0 : ℝ) < 2) n
  have h2n_ne : (2 : ℝ) ^ n ≠ 0 := ne_of_gt h2n_pos
  have hfactor : ∀ x : Fin n → Bool,
    (1 - f x * noiseOperator ρ f x) / 2 =
    (1 : ℝ) / 2 - (1 : ℝ) / 2 * (f x * noiseOperator ρ f x) := fun x => by ring
  simp_rw [hfactor]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, nsmul_eq_mul]
  simp_rw [← Finset.mul_sum]
  push_cast
  field_simp

end BooleanFourier

namespace BooleanFourier

/--
[noiseSensitivityReal_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/DisagreementStability.lean)
-/
@[path]
lemma noiseSensitivityReal_eq
  {n : ℕ}
  {δ : ℝ}
  {f : (Fin n → Bool) → ℝ} :
-- imply
  noiseSensitivityReal δ f = (1 - noiseStability (1 - 2 * δ) f) / 2 :=
-- proof
disagreementProb_eq (1 - 2 * δ) f

end BooleanFourier

namespace BooleanFourier

/--
[noiseSensitivity_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/DisagreementStability.lean)
-/
@[path]
lemma noiseSensitivity_eq
  {n : ℕ}
  {δ : ℝ}
  {f : (Fin n → Bool) → Bool} :
-- imply
  noiseSensitivity δ f = (1 - noiseStability (1 - 2 * δ) (fun x => boolToReal (f x))) / 2 := by
-- proof
  rfl

end BooleanFourier


-- created on 2026-10-23
