/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.NumberTheoryI.code.KroneckerWeber.Part5
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.KroneckerWeber
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.IdealFactorization
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.FinitePlaceAbsValue
import Theorem.v1.Atlas.NumberTheoryI.code.IdealFactorization.Part3
import Theorem.v1.Atlas.NumberTheoryI.code.FinitePlaceAbsValue
import Def.v1.Atlas.NumberTheoryI.code.RayClassFields.Part21


noncomputable section

open scoped NumberField

namespace RayClassField

variable {K : Type*} [Field K] [NumberField K]

universe u

attribute [instance] instFintypeSignsTimesUnits

omit [NumberField K] in
lemma signAtPlace_mul {w : NumberField.InfinitePlace K}
    (hw : w.IsReal) (a b : Kˣ) :
    signAtPlace hw (a * b) = signAtPlace hw a + signAtPlace hw b := by
  simp only [signAtPlace]
  have ha_im := embedding_im_zero hw (a : K)
  have hb_im := embedding_im_zero hw (b : K)
  have hab_re : (w.embedding ((a * b : Kˣ) : K)).re =
      (w.embedding (a : K)).re * (w.embedding (b : K)).re := by
    simp only [Units.val_mul, map_mul, Complex.mul_re, ha_im, hb_im, mul_zero, sub_zero]
  rw [hab_re]
  have ha_ne := embedding_re_ne_zero hw a
  have hb_ne := embedding_re_ne_zero hw b
  rcases lt_or_gt_of_ne ha_ne with ha_neg | ha_pos <;>
  rcases lt_or_gt_of_ne hb_ne with hb_neg | hb_pos
  · simp [not_lt.mpr ha_neg.le, not_lt.mpr hb_neg.le,
          mul_pos_of_neg_of_neg ha_neg hb_neg]; decide
  · simp [not_lt.mpr ha_neg.le, hb_pos,
          not_lt.mpr (mul_neg_of_neg_of_pos ha_neg hb_pos).le]
  · simp [ha_pos, not_lt.mpr hb_neg.le,
          not_lt.mpr (mul_neg_of_pos_of_neg ha_pos hb_neg).le]
  · simp [ha_pos, hb_pos, mul_pos ha_pos hb_pos]

omit [NumberField K] in
lemma signAtPlace_eq_zero_iff {w : NumberField.InfinitePlace K}
    (hw : w.IsReal) (α : Kˣ) :
    signAtPlace hw α = 0 ↔ 0 < (w.embedding (α : K)).re := by
  simp only [signAtPlace]
  constructor
  · intro h; split_ifs at h with hpos; exact hpos; exact absurd h one_ne_zero
  · intro h; simp [h]

end RayClassField
end
