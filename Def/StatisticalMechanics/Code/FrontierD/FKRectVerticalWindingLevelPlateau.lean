/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingLevelPlateau.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectVerticalWindingCutCollision
import Theorem.StatisticalMechanics.Code.FrontierD.IntegerUnitStepPlateau
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectVerticalWindingLevelPlateau
open SimpleGraph


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
