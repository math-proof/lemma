module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnAnnulusCharge.Part10
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDualBoundaryWiring
public import Instance.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnMixedAnnulusCharge


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnMixedAnnulusCharge.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

abbrev FKRectRawPrimalWiredDualHorizontalCrossingComponent
    (R : FKRectTorus) (omega : R.Configuration) :=
  FKRectRawPrimalHorizontalCrossingComponent R omega ⊕
    FKRectRawWiredDualHorizontalCrossingComponent R omega


end
end StatMech.FrontierD
