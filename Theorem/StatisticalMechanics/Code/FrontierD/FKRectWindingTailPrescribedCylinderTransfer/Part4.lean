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
import Def.StatisticalMechanics.Code.FrontierD.FKRectWindingTailPrescribedCylinderTransfer.Part4
open Finset
open scoped BigOperators


namespace StatMech.FrontierD

open StatMech

noncomputable section

theorem fkRectAfWindingTailPrescribedCylinderRepair_of_sourceWidth
    (R : FKRectTorus) (r : Nat) (I : Finset R.EdgeIndex)
    (hwidth : 2 * r ≤ R.width)
    (hrepair : FKRectWindingTailPrescribedCylinderRepair R r I
      (fkRectAfPair R) (fkRectAfBottomIndexSet R r)) :
    FKRectAfWindingTailPrescribedCylinderRepair R r I := by
  exact ⟨card_fkRectAfBottomIndexSet R r hwidth, hrepair⟩


theorem fkRectCriticalWindingTailMass_cFE_perimeter_le_afCylinderEvent
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q) (r perimeter : Nat)
    (I : Finset R.EdgeIndex) (hI : I.card ≤ perimeter)
    (hrepair : FKRectAfWindingTailPrescribedCylinderRepair R r I) :
    FK.cFE (fkRectCriticalP q) q ^ perimeter *
        fkRectCriticalWindingTailMass R q r ≤
      (2 ^ perimeter : Nat) *
        StatMech.Probability.finiteEventMass
          (FK.fkProb (fkRectHorizontalCylinderGraph R)
            (fkRectCriticalP q) q)
          {rho | FKRectHorizontalCylinderDistinctPairedWitness R
            (fkRectAfPair R) (fkRectAfBottomIndexSet R r) rho} := by
  exact
    fkRectCriticalWindingTailMass_cFE_perimeter_le_prescribedCylinder
      R hq r perimeter I (fkRectAfPair R)
      (fkRectAfBottomIndexSet R r) hI hrepair.2

end
end StatMech.FrontierD
