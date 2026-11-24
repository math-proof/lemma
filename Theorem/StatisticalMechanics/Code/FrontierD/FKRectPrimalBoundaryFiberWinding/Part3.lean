module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryToggleMergeWinding
public import Theorem.StatisticalMechanics.Code.FrontierD.PermCycleQuotientWeightSum
public import Def.StatisticalMechanics.Code.FrontierD.FKRectPrimalBoundaryFiberWinding.Part2
open Equiv Finset SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalBoundaryFiberWinding.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

@[simp] theorem fkRectBlackBoundaryCycleWinding_mk
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    fkRectBlackBoundaryCycleWinding R omega (Quot.mk _ d) =
      fkRectBlackBoundaryCycleClassWinding R
        (fkRectConfigurationToMedialPairing R omega) d := by
  exact permCycleQuotientWeightSum_mk _ _ _


end
end StatMech.FrontierD
