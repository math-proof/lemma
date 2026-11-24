module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitRibbonEmbedding.Part5
public import Def.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitRibbonParity


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonParity.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

open StatMech.Onsager

open StatMech.Onsager.BaseCase

noncomputable section

theorem fkRectBlackOrbitMedialRibbonFlatSite_injective
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    Function.Injective
      (fkRectBlackOrbitMedialRibbonFlatSite R omega d) :=
  (fkRectBlackOrbitMedialRibbonIndexedSite_injective R omega d).comp
    (fkRectBlackOrbitMedialRibbonIndexEquiv R omega d).injective

end
end StatMech.FrontierD
