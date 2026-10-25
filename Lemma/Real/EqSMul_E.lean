import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.CoxeterGroup.InversionSet
import Lemma.List.In_BilinInversions_ListB.is.Lt_0
open Finset BigOperators List CoxeterGroup


namespace CoxeterGroup

/--
[neg_e_eq_neg_one_smul_e](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/InversionMultiplication.lean)
-/
@[path]
private lemma neg_e_eq_neg_one_smul_e
  [DecidableEq B]
  [Fintype B]
  {s : B} :
-- imply
  (fun t => -(e s t)) = (-1 : ℝ) • e s := by
-- proof
  ext t
  simp [Pi.smul_apply, smul_eq_mul]

end CoxeterGroup

namespace CoxeterGroup

/--
[wordSigma_append_s_component_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/InversionMultiplication.lean)
-/
@[path]
private lemma wordSigma_append_s_component_neg
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {word : List B}
  {s : B} :
-- imply
  wordSigma M (word ++ [s]) (e s) s = -(wordSigma M word (e s) s) := by
-- proof
  rw [wordSigma_append, wordSigma_singleton, sigma_e_self, neg_e_eq_neg_one_smul_e,
    wordSigma_smul]
  simp [Pi.smul_apply, smul_eq_mul]

end CoxeterGroup

namespace CoxeterGroup

/--
[bilinInversions_append_toggle](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/InversionMultiplication.lean)
-/
@[path]
private lemma bilinInversions_append_toggle
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {word : List B}
  {s : B}
-- given
  (hne : wordSigma M word (e s) s ≠ 0) :
-- imply
  s ∈ bilinInversions M (word ++ [s]) ↔ s ∉ bilinInversions M word := by
-- proof
  rw [In_BilinInversions_ListB.is.Lt_0, In_BilinInversions_ListB.is.Lt_0]
  rw [wordSigma_append_s_component_neg]
  constructor
  ·
    intro h_neg_lt h_lt
    linarith
  ·
    intro h_not_lt
    have h_not_lt' : ¬ wordSigma M word (e s) s < 0 := h_not_lt
    have h_ge : wordSigma M word (e s) s ≥ 0 := le_of_not_gt h_not_lt'
    have hpos : wordSigma M word (e s) s > 0 := lt_of_le_of_ne h_ge (Ne.symm hne)
    linarith

end CoxeterGroup


-- created on 2026-10-23
-- updated on 2026-10-24
