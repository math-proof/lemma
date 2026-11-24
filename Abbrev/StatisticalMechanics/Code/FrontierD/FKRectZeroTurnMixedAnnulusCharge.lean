module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnAnnulusCharge.Part10
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDualBoundaryWiring


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

abbrev FKRectRawWiredDualHorizontalCrossingComponent
    (R : FKRectTorus) (omega : R.Configuration) :=
  {C : (fkRectOpenGraph R
      (fkRectDualConfigurationEquiv R
        (fkRectForceCutClosed R omega))).ConnectedComponent //
    FKRectRawHorizontalCrossingComponent R
      (fkRectDualConfigurationEquiv R
        (fkRectForceCutClosed R omega)) C}

end
end StatMech.FrontierD
