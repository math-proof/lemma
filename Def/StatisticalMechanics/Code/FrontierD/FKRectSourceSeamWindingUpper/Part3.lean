module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectSourceSeamBarrier.Part4
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRankOneWindingTail
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryVerticalFlux.Part3
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectAugmentedBarrierPatternCost
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectSourceSeamWindingUpper.Part2
open SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSourceSeamWindingUpper.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def fkRectMedialLoopCutColumnContribution
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKMedialLoop R.medialTorus
      (fkRectConfigurationToMedialPairing R omega))
    (x : Fin R.width) (b : Bool) : Int := by
  classical
  exact if (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk
        (fkMedialVerticalSeamDart R.medialTorus
          (fkRectCutMedialColumn R x b)) = C then
    fkMedialCanonicalVerticalSeamSign R.medialTorus
      (fkRectCutMedialColumn R x b)
  else 0


end
end StatMech.FrontierD
