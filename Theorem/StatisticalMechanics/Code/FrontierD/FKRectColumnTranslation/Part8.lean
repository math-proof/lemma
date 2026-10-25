/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectColumnTranslation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectOrientedEvenRowBlock.Part3
import Structure.StatisticalMechanics.Code.FrontierD.FKRectColumnTranslation
open Set SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkRectColumnTranslate_one_val_of_lt
    (R : FKRectTorus) (x : Fin R.width)
    (hlt : x.val + 1 < R.width) :
    (fkRectColumnTranslate R 1 x).val = x.val + 1 := by
  change (((x.val : Int) + 1).natMod R.width : Nat) = x.val + 1
  rw [Int.natMod, Int.emod_eq_of_lt (by omega) (by exact_mod_cast hlt)]
  exact_mod_cast Int.toNat_of_nonneg (show 0 ≤ (x.val : Int) + 1 by omega)

theorem fkRectEvenRowTranslation_columnTranslation_comm
    (R : FKRectTorus) (step : Nat) (s : Int) (v : R.Vertex) :
    fkRectEvenRowTranslationVertexEquiv R step
        (fkRectColumnTranslationVertexEquiv R s v) =
      fkRectColumnTranslationVertexEquiv R s
        (fkRectEvenRowTranslationVertexEquiv R step v) := by
  rfl


end
end StatMech.FrontierD
