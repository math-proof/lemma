/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderTransverseTail.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderTransverseDiagonalBound
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderTailLaw
import Def.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderTransverseTail


namespace StatMech.FrontierD

noncomputable section

theorem fkRectCriticalWindingTailMass_cFE_le_crossingPrefactor_mul_sqrtExact
    {q : Real} (hq : 4 < q) (R : FKRectTorus)
    (r : Nat) (hr : 0 < r)
    (hcross : FKRectWindingTailForcesHorizontalCylinderCrossings R r) :
    FK.cFE (fkRectCriticalP q) q ^ (2 * R.width) *
        fkRectCriticalWindingTailMass R q r <=
      Nat.choose R.width r * R.width ^ R.width *
        Real.sqrt
          (fkQgt4CriticalFreeExactDiagonalTwoPoint hq (R.height - 1)) ^
            (r - 1) := by
  let Source : Set R.Configuration :=
    {omega | r <= fkRectUnorientedVerticalWindingNumber R omega}
  let Target : Set R.Configuration :=
    {eta | r <= fkRectHorizontalCutPrimalCrossingClusterCount R
      (fkRectForceHorizontalCutClosed R eta)}
  have htransfer :=
    fkRectCritical_eventMass_le_horizontalCutEventMass_of_force R
      (by linarith : (1 : Real) <= q) Source Target (by
        intro omega homega
        change r <= fkRectHorizontalCutPrimalCrossingClusterCount R
          (fkRectForceHorizontalCutClosed R
            (fkRectForceHorizontalCutClosed R omega))
        rw [fkRectHorizontalCutClosedConfiguration_force_eq_self R
          (fkRectForceHorizontalCutClosed R omega)
          (fkRectHorizontalCutClosedConfiguration_force R omega)]
        exact hcross omega homega)
  rw [show fkRectCriticalEventMass R q Source =
      fkRectCriticalWindingTailMass R q r by
        symm
        exact fkRectCriticalWindingTailMass_eq_eventMass R q r] at htransfer
  exact htransfer.trans
    (fkRectCriticalHorizontalCut_crossingTail_le_sqrtExact_pow_pred
      hq R r hr)

end
end StatMech.FrontierD
