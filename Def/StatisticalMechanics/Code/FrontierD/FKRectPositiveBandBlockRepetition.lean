module
public import Def.StatisticalMechanics.Code.FrontierD.FKRectColumnTranslation.Part8
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDualBarrierLocalizedCycle
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDualBarrierForceTopology
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDualSourceBarrierPattern
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDualSourceBarrierRate
public import Theorem.StatisticalMechanics.Code.FK.TwoPointPathLower
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

def fkRectPositiveBandBulkBlocks
    {R : FKRectTorus} {q : Real} {scale : Nat}
    (B : FKRectPositiveBandOrientedBlock R q scale) : Nat :=
  (R.height - 1 - (24 * scale + 4)) / B.step

end
end StatMech.FrontierD
