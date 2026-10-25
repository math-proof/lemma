/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEvenRowTranslation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedAxisSource
import Def.StatisticalMechanics.Code.FrontierD.FKRectEvenRowTranslation
open Set SimpleGraph StatMech.Lattice


namespace StatMech.FrontierD

noncomputable section

theorem fkRectRowTranslate_neg_left
    (R : FKRectTorus) (s : Int) (y : Fin R.height) :
    fkRectRowTranslate R (-s) (fkRectRowTranslate R s y) = y := by
  apply Fin.ext
  apply Nat.ModEq.eq_of_lt_of_lt
  · apply (ZMod.natCast_eq_natCast_iff _ _ R.height).mp
    simp only [fkRectRowTranslate]
    rw [fkRectIntModFin_cast]
    push_cast
    rw [fkRectIntModFin_cast]
    push_cast
    ring
  · exact (fkRectRowTranslate R (-s) (fkRectRowTranslate R s y)).isLt
  · exact y.isLt

theorem fkRectRowTranslate_neg_right
    (R : FKRectTorus) (s : Int) (y : Fin R.height) :
    fkRectRowTranslate R s (fkRectRowTranslate R (-s) y) = y := by
  simpa only [neg_neg] using fkRectRowTranslate_neg_left R (-s) y


end
end StatMech.FrontierD
