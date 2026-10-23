import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.BooleanFunctions.code.Theorems
open Finset BigOperators BooleanFourier


/--
[vol_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Theorems.lean)
-/
@[path]
private lemma vol_nonneg_eq
  {n : ℕ}
  {f : (Fin n → Bool) → Bool} :
-- imply
  0 ≤ vol f := by
-- proof
  apply BooleanFourier.vol_nonneg f

/--
[vol_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Theorems.lean)
-/
@[path]
private lemma vol_le_one_eq
  {n : ℕ}
  {f : (Fin n → Bool) → Bool} :
-- imply
  vol f ≤ 1 := by
-- proof
  apply BooleanFourier.vol_le_one f

/--
[parseval_signed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Theorems.lean)
-/
@[path]
private lemma parseval_signed_eq
  {n : ℕ}
  {f : (Fin n → Bool) → Bool} :
-- imply
  ∑ S : Finset (Fin n), fourierCoeff (fun x => boolToReal (f x)) S ^ 2 = 1 := by
-- proof
  apply BooleanFourier.parseval_signed f

/--
[boolToReal_agreement_indicator](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Theorems.lean)
-/
@[path]
private lemma boolToReal_agreement_indicator_eq
  {n : ℕ}
  {f : (Fin n → Bool) → Bool}
  {x y : Fin n → Bool} :
-- imply
  (if boolToReal (f x) * boolToReal (f y) = boolToReal (f (boolMul x y)) then (1 : ℝ) else 0) = (1 + boolToReal (f x) * boolToReal (f y) * boolToReal (f (boolMul x y))) / 2 := by
-- proof
  apply BooleanFourier.boolToReal_agreement_indicator f x y

/--
[tripleCorrelation_eq_sum_cube](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Theorems.lean)
-/
@[path]
private lemma tripleCorrelation_eq_sum_cube_eq
  {n : ℕ}
  {g : (Fin n → Bool) → ℝ} :
-- imply
  (1 / (2 : ℝ) ^ n) ^ 2 * ∑ x : Fin n → Bool, ∑ y : Fin n → Bool, g x * g y * g (boolMul x y) = ∑ S : Finset (Fin n), fourierCoeff g S ^ 3 := by
-- proof
  apply BooleanFourier.tripleCorrelation_eq_sum_cube g

/--
[agreementProb_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Theorems.lean)
-/
@[path]
private lemma agreementProb_eq_eq
  {n : ℕ}
  {f : (Fin n → Bool) → Bool} :
-- imply
  agreementProb f = (1 + ∑ S : Finset (Fin n), fourierCoeff (fun x => boolToReal (f x)) S ^ 3) / 2 := by
-- proof
  apply BooleanFourier.agreementProb_eq f

/--
[flipCoord_eq_flipAt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Theorems.lean)
-/
@[path]
private lemma flipCoord_eq_flipAt_eq
  {n : ℕ}
  {x : Fin n → Bool}
  {i : Fin n} :
-- imply
  flipCoord x i = flipAt i x := by
-- proof
  apply flipCoord_eq_flipAt x i

/--
[influence_eq_influenceReal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Theorems.lean)
-/
@[path]
private lemma influence_eq_influenceReal_eq
  {n : ℕ}
  {f : (Fin n → Bool) → Bool}
  {i : Fin n} :
-- imply
  influence f i = influenceReal (fun x => boolToReal (f x)) i := by
-- proof
  apply influence_eq_influenceReal f i

/--
[totalInfluence_eq_totalInfluenceReal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Theorems.lean)
-/
@[path]
private lemma totalInfluence_eq_totalInfluenceReal_eq
  {n : ℕ}
  {f : (Fin n → Bool) → Bool} :
-- imply
  totalInfluence f = totalInfluenceReal (fun x => boolToReal (f x)) := by
-- proof
  apply totalInfluence_eq_totalInfluenceReal f

/--
[totalInfluence_eq_weighted_fourier'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Theorems.lean)
-/
@[path]
private lemma totalInfluence_eq_weighted_fourier'_eq
  {n : ℕ}
  {f : (Fin n → Bool) → Bool} :
-- imply
  totalInfluence f = ∑ S : Finset (Fin n), (S.card : ℝ) * fourierCoeff (fun x => boolToReal (f x)) S ^ 2 := by
-- proof
  apply totalInfluence_eq_weighted_fourier' f

/--
[exists_fourierCoeff_ge_of_sum_cube_ge](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Theorems.lean)
-/
@[path]
private lemma exists_fourierCoeff_ge_of_sum_cube_ge_eq
  {n : ℕ}
  {f : (Fin n → Bool) → Bool}
  {δ : ℝ}
-- given
  (hδ : ∑ S : Finset (Fin n), fourierCoeff (fun x => boolToReal (f x)) S ^ 3 ≥ 2 * δ) :
-- imply
  ∃ S : Finset (Fin n), fourierCoeff (fun x => boolToReal (f x)) S ≥ 2 * δ := by
-- proof
  apply BooleanFourier.exists_fourierCoeff_ge_of_sum_cube_ge f δ hδ

/--
[exists_fourierCoeff_ge_of_agreementProb](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Theorems.lean)
-/
@[path]
private lemma exists_fourierCoeff_ge_of_agreementProb_eq
  {n : ℕ}
  {f : (Fin n → Bool) → Bool}
  {δ : ℝ}
-- given
  (hδ : agreementProb f ≥ 1/2 + δ) :
-- imply
  ∃ S : Finset (Fin n), fourierCoeff (fun x => boolToReal (f x)) S ≥ 2 * δ := by
-- proof
  apply BooleanFourier.exists_fourierCoeff_ge_of_agreementProb f δ hδ


-- created on 2026-10-23
