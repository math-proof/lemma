/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnAnnulusCharge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnCutInjection.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnAnnulusCharge.Part3


namespace StatMech.FrontierD

noncomputable section

noncomputable def fkRectRawPrimalCrossingTorusComponent
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectRawPrimalHorizontalCrossingComponent R omega) :
    (fkRectOpenGraph R omega).ConnectedComponent :=
  SimpleGraph.ConnectedComponent.map
    (SimpleGraph.Hom.ofLE (fkRectOpenGraph_forceCutClosed_le R omega)) C.1

end
end StatMech.FrontierD
