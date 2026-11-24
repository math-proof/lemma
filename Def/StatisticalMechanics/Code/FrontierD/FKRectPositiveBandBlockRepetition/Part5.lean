module
public import Def.StatisticalMechanics.Code.FrontierD.FKRectColumnTranslation.Part8
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDualBarrierLocalizedCycle
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDualBarrierForceTopology
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDualSourceBarrierPattern
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDualSourceBarrierRate
public import Theorem.StatisticalMechanics.Code.FK.TwoPointPathLower
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPositiveBandBlockRepetition.Part4
open Set SimpleGraph Filter Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPositiveBandBlockRepetition.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def fkRectPositiveBandBlockBottomConnectorEvent
    {R : FKRectTorus} {q : Real} {scale : Nat}
    (B : FKRectPositiveBandOrientedBlock R q scale)
    (hheight : 24 * scale + 4 ≤ R.height - 1) :
    Set R.Configuration :=
  {omega | FKRectConnectedWithin R omega
    (fkRectColumnBand R 1 (4 * scale + 1) 1 (R.height - 1))
    (fkRectColumnBandRowOne R 1 (4 * scale + 1)
      (fkRectUnitGapColumn R) (by rfl)
        (by simp [fkRectUnitGapColumn]))
    (fkRectPositiveBandBlockPathVertex B hheight 0)}


def fkRectPositiveBandBlockTopConnectorEvent
    {R : FKRectTorus} {q : Real} {scale : Nat}
    (B : FKRectPositiveBandOrientedBlock R q scale)
    (hheight : 24 * scale + 4 ≤ R.height - 1) :
    Set R.Configuration :=
  {omega | FKRectConnectedWithin R omega
    (fkRectColumnBand R 1 (4 * scale + 1) 1 (R.height - 1))
    (fkRectPositiveBandBlockPathVertex B hheight
      (Fin.last (fkRectPositiveBandBulkBlocks B)))
    (fkRectColumnBandLastRow R 1 (4 * scale + 1)
      (fkRectUnitGapColumn R) (by rfl)
        (by simp [fkRectUnitGapColumn]))}

end
end StatMech.FrontierD
