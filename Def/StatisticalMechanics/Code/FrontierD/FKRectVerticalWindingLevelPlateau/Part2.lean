/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingLevelPlateau.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectVerticalWindingCutCollision
import Theorem.StatisticalMechanics.Code.FrontierD.IntegerUnitStepPlateau
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectVerticalWindingLevelPlateau.Part2
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

noncomputable def fkRectBlackBoundaryUnitCutComponent
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus)
    (hpos : 0 < (fkRectWalkWinding R
      (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2)
    (j : Fin (fkRectWalkWinding R
      (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2.toNat) :
    (fkRectOpenGraph R
      (fkRectForceHorizontalCutClosed R omega)).ConnectedComponent :=
  let pairing := fkRectConfigurationToMedialPairing R omega
  let a := (fkRectBlackBoundaryUnitPlateauEndpoints R omega d hpos j).1
  (fkRectOpenGraph R
    (fkRectForceHorizontalCutClosed R omega)).connectedComponentMk
      (fkRectMedialDartPrimalLabel R
        ((fkMedialBoundaryStep pairing)^[a] d.1))


end
end StatMech.FrontierD
