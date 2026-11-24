module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectVerticalWindingCutCollision
public import Theorem.StatisticalMechanics.Code.FrontierD.IntegerUnitStepPlateau
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectVerticalWindingLevelPlateau
open SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingLevelPlateau.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

noncomputable def fkRectBlackBoundaryUnitPlateauEndpoints
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus)
    (hpos : 0 < (fkRectWalkWinding R
      (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2)
    (j : Fin (fkRectWalkWinding R
      (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2.toNat) :
    Nat × Nat :=
  Classical.choose
    (exists_fkRectBlackBoundaryUnitPlateauEndpoints R omega d hpos j)


end
end StatMech.FrontierD
