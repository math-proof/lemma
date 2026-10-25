/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPositiveBandBlockRepetition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.FKRectColumnTranslation.Part8
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDualBarrierLocalizedCycle
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDualBarrierForceTopology
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDualSourceBarrierPattern
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDualSourceBarrierRate
import Theorem.StatisticalMechanics.Code.FK.TwoPointPathLower
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPositiveBandBlockRepetition.Part2
open Set SimpleGraph Filter Topology


namespace StatMech.FrontierD

noncomputable section

def fkRectPositiveBandBlockBulkPairs
    {R : FKRectTorus} {q : Real} {scale : Nat}
    (B : FKRectPositiveBandOrientedBlock R q scale)
    (hheight : 24 * scale + 4 ≤ R.height - 1) :=
  connectionPathPairs (fkRectPositiveBandBulkBlocks B)
    (fkRectPositiveBandBlockPathVertex B hheight)


def fkRectPositiveBandBlockConnectorPairs
    {R : FKRectTorus} {q : Real} {scale : Nat}
    (B : FKRectPositiveBandOrientedBlock R q scale)
    (hheight : 24 * scale + 4 ≤ R.height - 1) :
    Finset
      (FKRectColumnBandVertex R 1 (4 * scale + 1) 1 (R.height - 1) ×
        FKRectColumnBandVertex R 1 (4 * scale + 1) 1 (R.height - 1)) :=
  { (fkRectColumnBandRowOne R 1 (4 * scale + 1)
        (fkRectUnitGapColumn R) (by rfl)
          (by simp [fkRectUnitGapColumn]),
      fkRectPositiveBandBlockPathVertex B hheight 0),
    (fkRectPositiveBandBlockPathVertex B hheight
        (Fin.last (fkRectPositiveBandBulkBlocks B)),
      fkRectColumnBandLastRow R 1 (4 * scale + 1)
        (fkRectUnitGapColumn R) (by rfl)
          (by simp [fkRectUnitGapColumn])) }


def fkRectPositiveBandBlockAuxiliaryPairs
    {R : FKRectTorus} {q : Real} {scale : Nat}
    (B : FKRectPositiveBandOrientedBlock R q scale)
    (hheight : 24 * scale + 4 ≤ R.height - 1) :=
  fkRectPositiveBandBlockBulkPairs B hheight ∪
    fkRectPositiveBandBlockConnectorPairs B hheight


end
end StatMech.FrontierD
