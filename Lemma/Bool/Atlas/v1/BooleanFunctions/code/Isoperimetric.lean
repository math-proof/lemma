import Mathlib
import sympy.Basic
import Def.v1.Atlas.BooleanFunctions.code.Theorems
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.Theorems
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.InfluenceFourier
import Def.v1.Atlas.BooleanFunctions.code.InfluenceFourier
open Finset BigOperators Real


namespace BooleanFourier

/--
[sum_boolToReal_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Isoperimetric.lean)
-/
@[path]
lemma sum_boolToReal_eq
  {n : ℕ}
  {f : (Fin n → Bool) → Bool} :
-- imply
  ∑ x : Fin n → Bool, boolToReal (f x) = 2 * ((Finset.univ.filter fun x => f x = true).card : ℝ) - (2 : ℝ) ^ n := by
-- proof
  have hterm : ∀ x : Fin n → Bool,
    boolToReal (f x) = 2 * (if f x = true then (1 : ℝ) else 0) - 1 := by
    intro x
    cases hfx : f x
    · simp [boolToReal]
    · simp [boolToReal]; norm_num
  simp_rw [hterm, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul, mul_one,
    ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_boole]
  push_cast
  rfl

end BooleanFourier

namespace BooleanFourier

/--
[fourierCoeff_empty_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Isoperimetric.lean)
-/
@[path]
lemma fourierCoeff_empty_eq
  {n : ℕ}
  {f : (Fin n → Bool) → Bool} :
-- imply
  fourierCoeff (fun x => boolToReal (f x)) ∅ = 2 * vol f - 1 := by
-- proof
  unfold fourierCoeff vol
  simp only [chi, Finset.prod_empty, mul_one, one_div]
  have h2n : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero n (by norm_num : (2 : ℝ) ≠ 0)
  rw [sum_boolToReal_eq]
  field_simp

end BooleanFourier

namespace BooleanFourier

/--
[varianceReal_boolToReal_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Isoperimetric.lean)
-/
@[path]
lemma varianceReal_boolToReal_eq
  {n : ℕ}
  {f : (Fin n → Bool) → Bool} :
-- imply
  varianceReal (fun x => boolToReal (f x)) = 4 * vol f * (1 - vol f) := by
-- proof
  classical
  set g : (Fin n → Bool) → ℝ := fun x => boolToReal (f x) with hg_def
  have hvar_split : varianceReal g =
    ∑ S : Finset (Fin n), fourierCoeff g S ^ 2 - fourierCoeff g ∅ ^ 2 := by
    unfold varianceReal
    have herase : (Finset.univ : Finset (Finset (Fin n))).filter (· ≠ ∅) =
      Finset.univ.erase ∅ := by
      ext S; simp [Finset.mem_erase, Finset.mem_filter]
    rw [herase]
    have hsplit := Finset.sum_erase_add (Finset.univ : Finset (Finset (Fin n)))
      (fun S => fourierCoeff g S ^ 2) (Finset.mem_univ ∅)
    linarith
  have hparseval : ∑ S : Finset (Fin n), fourierCoeff g S ^ 2 = 1 :=
    parseval_signed f
  have hempty : fourierCoeff g ∅ = 2 * vol f - 1 :=
    fourierCoeff_empty_eq f
  rw [hvar_split, hparseval, hempty]
  ring

end BooleanFourier

namespace BooleanFourier

/--
[edge_isoperimetric_inequality](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Isoperimetric.lean)
-/
@[path]
lemma edge_isoperimetric_inequality
  {n : ℕ}
  {f : (Fin n → Bool) → Bool} :
-- imply
  totalInfluence f ≥ 4 * vol f * (1 - vol f) := by
-- proof
  set g : (Fin n → Bool) → ℝ := fun x => boolToReal (f x) with hg_def
  have h_eq : totalInfluence f = totalInfluenceReal g :=
    totalInfluence_eq_totalInfluenceReal f
  have h_ge_var : totalInfluenceReal g ≥ varianceReal g :=
    totalInfluenceReal_ge_varianceReal g
  have h_var : varianceReal g = 4 * vol f * (1 - vol f) :=
    varianceReal_boolToReal_eq f
  linarith

end BooleanFourier

namespace BooleanFourier

/--
[corollary_3_2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Isoperimetric.lean)
-/
@[path]
lemma corollary_3_2
  {n : ℕ}
  {f : (Fin n → Bool) → Bool} :
-- imply
  4 * vol f * (1 - vol f) ≤ totalInfluence f :=
-- proof
  edge_isoperimetric_inequality f

end BooleanFourier


-- created on 2026-10-23
