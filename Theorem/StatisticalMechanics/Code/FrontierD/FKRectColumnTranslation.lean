/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectColumnTranslation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectOrientedEvenRowBlock.Part3
import Def.StatisticalMechanics.Code.FrontierD.FKRectColumnTranslation
open Set SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkRectColumnTranslate_neg_left
    (R : FKRectTorus) (s : Int) (x : Fin R.width) :
    fkRectColumnTranslate R (-s) (fkRectColumnTranslate R s x) = x := by
  apply Fin.ext
  apply Nat.ModEq.eq_of_lt_of_lt
  · apply (ZMod.natCast_eq_natCast_iff _ _ R.width).mp
    simp only [fkRectColumnTranslate]
    rw [fkRectIntModFin_cast]
    push_cast
    rw [fkRectIntModFin_cast]
    push_cast
    ring
  · exact (fkRectColumnTranslate R (-s) (fkRectColumnTranslate R s x)).isLt
  · exact x.isLt

theorem fkRectColumnTranslate_neg_right
    (R : FKRectTorus) (s : Int) (x : Fin R.width) :
    fkRectColumnTranslate R s (fkRectColumnTranslate R (-s) x) = x := by
  simpa only [neg_neg] using fkRectColumnTranslate_neg_left R (-s) x


end
end StatMech.FrontierD
