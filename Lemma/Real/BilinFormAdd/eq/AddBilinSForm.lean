import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.CoxeterGroup.GeometricRepresentation
open Finset BigOperators CoxeterGroup


/--
[bilinForm_add_left](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/GeometricRepresentation.lean)
-/
@[path]
private lemma bilinForm_add_left_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {v₁ v₂ w : B → ℝ} :
-- imply
  bilinForm M (v₁ + v₂) w = bilinForm M v₁ w + bilinForm M v₂ w := by
-- proof
  apply CoxeterGroup.bilinForm_add_left M v₁ v₂ w

/--
[bilinForm_smul_left](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/GeometricRepresentation.lean)
-/
@[path]
private lemma bilinForm_smul_left_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {c : ℝ}
  {v w : B → ℝ} :
-- imply
  bilinForm M (c • v) w = c * bilinForm M v w := by
-- proof
  apply CoxeterGroup.bilinForm_smul_left M c v w

/--
[sigma_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/GeometricRepresentation.lean)
-/
@[path]
private lemma sigma_add_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s : B}
  {v₁ v₂ : B → ℝ} :
-- imply
  sigma M s (v₁ + v₂) = sigma M s v₁ + sigma M s v₂ := by
-- proof
  apply CoxeterGroup.sigma_add M s v₁ v₂

/--
[sigma_smul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/GeometricRepresentation.lean)
-/
@[path]
private lemma sigma_smul_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s : B}
  {c : ℝ}
  {v : B → ℝ} :
-- imply
  sigma M s (c • v) = c • sigma M s v := by
-- proof
  apply CoxeterGroup.sigma_smul M s c v

/--
[bilinForm_sigma_e](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/GeometricRepresentation.lean)
-/
@[path]
private lemma bilinForm_sigma_e_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s : B}
  {v : B → ℝ} :
-- imply
  bilinForm M (sigma M s v) (e s) = -(bilinForm M v (e s)) := by
-- proof
  apply CoxeterGroup.bilinForm_sigma_e M s v

/--
[sigma_involution](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/GeometricRepresentation.lean)
-/
@[path]
private lemma sigma_involution_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s : B}
  {v : B → ℝ} :
-- imply
  sigma M s (sigma M s v) = v := by
-- proof
  apply CoxeterGroup.sigma_involution M s v

/--
[sigmaLinearEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/GeometricRepresentation.lean)
-/
@[path]
private lemma sigmaLinearEquiv_apply_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s : B}
  {v : B → ℝ} :
-- imply
  sigmaLinearEquiv M s v = sigma M s v := by
-- proof
  apply CoxeterGroup.sigmaLinearEquiv_apply M s v

/--
[bilinForm_add_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/GeometricRepresentation.lean)
-/
@[path]
private lemma bilinForm_add_right_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {v w₁ w₂ : B → ℝ} :
-- imply
  bilinForm M v (w₁ + w₂) = bilinForm M v w₁ + bilinForm M v w₂ := by
-- proof
  apply CoxeterGroup.bilinForm_add_right M v w₁ w₂

/--
[bilinForm_smul_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/GeometricRepresentation.lean)
-/
@[path]
private lemma bilinForm_smul_right_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {v : B → ℝ}
  {c : ℝ}
  {w : B → ℝ} :
-- imply
  bilinForm M v (c • w) = c * bilinForm M v w := by
-- proof
  apply CoxeterGroup.bilinForm_smul_right M v c w

/--
[bilinForm_symm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/GeometricRepresentation.lean)
-/
@[path]
private lemma bilinForm_symm_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {v w : B → ℝ} :
-- imply
  bilinForm M v w = bilinForm M w v := by
-- proof
  apply CoxeterGroup.bilinForm_symm M v w

/--
[sigma_preserves_form](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/GeometricRepresentation.lean)
-/
@[path]
private lemma sigma_preserves_form_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s : B}
  {v w : B → ℝ} :
-- imply
  bilinForm M (sigma M s v) (sigma M s w) = bilinForm M v w := by
-- proof
  apply CoxeterGroup.sigma_preserves_form M s v w

/--
[wordSigma_nil](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/GeometricRepresentation.lean)
-/
@[path]
private lemma wordSigma_nil_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {v : B → ℝ} :
-- imply
  wordSigma M [] v = v := by
-- proof
  apply CoxeterGroup.wordSigma_nil M v

/--
[wordSigma_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/GeometricRepresentation.lean)
-/
@[path]
private lemma wordSigma_singleton_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s : B}
  {v : B → ℝ} :
-- imply
  wordSigma M [s] v = sigma M s v := by
-- proof
  apply CoxeterGroup.wordSigma_singleton M s v

/--
[wordSigma_cons](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/GeometricRepresentation.lean)
-/
@[path]
private lemma wordSigma_cons_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s : B}
  {rest : List B}
  {v : B → ℝ} :
-- imply
  wordSigma M (s :: rest) v = sigma M s (wordSigma M rest v) := by
-- proof
  apply CoxeterGroup.wordSigma_cons M s rest v

/--
[wordSigma_append](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/GeometricRepresentation.lean)
-/
@[path]
private lemma wordSigma_append_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {w₁ w₂ : List B}
  {v : B → ℝ} :
-- imply
  wordSigma M (w₁ ++ w₂) v = wordSigma M w₁ (wordSigma M w₂ v) := by
-- proof
  apply CoxeterGroup.wordSigma_append M w₁ w₂ v

/--
[wordSigma_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/GeometricRepresentation.lean)
-/
@[path]
private lemma wordSigma_add_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {word : List B}
  {v₁ v₂ : B → ℝ} :
-- imply
  wordSigma M word (v₁ + v₂) = wordSigma M word v₁ + wordSigma M word v₂ := by
-- proof
  apply CoxeterGroup.wordSigma_add M word v₁ v₂

/--
[wordSigma_smul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/GeometricRepresentation.lean)
-/
@[path]
private lemma wordSigma_smul_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {word : List B}
  {c : ℝ}
  {v : B → ℝ} :
-- imply
  wordSigma M word (c • v) = c • wordSigma M word v := by
-- proof
  apply CoxeterGroup.wordSigma_smul M word c v

/--
[wordSigma_preserves_form](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/GeometricRepresentation.lean)
-/
@[path]
private lemma wordSigma_preserves_form_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {word : List B}
  {v w : B → ℝ} :
-- imply
  bilinForm M (wordSigma M word v) (wordSigma M word w) = bilinForm M v w := by
-- proof
  apply CoxeterGroup.wordSigma_preserves_form M word v w

/--
[sigma_e_other](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/GeometricRepresentation.lean)
-/
@[path]
private lemma sigma_e_other_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s t : B} :
-- imply
  sigma M s (e t) = fun u => e t u - 2 * formVal M t s * e s u := by
-- proof
  apply CoxeterGroup.sigma_e_other M s t


-- created on 2026-10-23
