/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingTailPrescribedCylinderTransfer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectIndexedPatternPushforward.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderCrossings.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRandomClusterEventFKG.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusWindingCountBridge.Part5
import Def.StatisticalMechanics.Code.FrontierD.FKRectWindingTailPrescribedCylinderTransfer.Part3
open Finset
open scoped BigOperators


namespace StatMech.FrontierD

open StatMech

noncomputable section

theorem card_fkRectAfBottomIndexSet
    (R : FKRectTorus) (r : Nat) (hwidth : 2 * r ≤ R.width) :
    (fkRectAfBottomIndexSet R r).card = r := by
  unfold fkRectAfBottomIndexSet
  rw [Finset.card_image_iff.mpr]
  · simp
  · intro i hi j hj hij
    have hi' : i < r := by simpa using hi
    have hj' : j < r := by simpa using hj
    have hiWidth : i + 1 < R.width := by
      omega
    have hjWidth : j + 1 < R.width := by
      omega
    have hval := congrArg Fin.val hij
    simp [fkRectAfBottomIndex, Nat.mod_eq_of_lt hiWidth,
      Nat.mod_eq_of_lt hjWidth] at hval
    omega


end
end StatMech.FrontierD
