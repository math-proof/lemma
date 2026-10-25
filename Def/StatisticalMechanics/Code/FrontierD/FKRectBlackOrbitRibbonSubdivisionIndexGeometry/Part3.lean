/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonSubdivisionIndexGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitRibbonSubdivisionCodeInjective
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectListFlatMapReplicate
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitRibbonSubdivisionIndexGeometry.Part2


namespace StatMech.FrontierD

open StatMech.Onsager

open StatMech.Onsager.BaseCase

noncomputable section

def fkRectBlackOrbitRibbonSubdivisionSite
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus)
    (z : FKRectBlackOrbitRibbonSubdivisionIndex R omega d) :
    ZMod (fkRectBlackOrbitRibbonSubdivisionSide R) ×
      ZMod (fkRectBlackOrbitRibbonSubdivisionSide R) := by
  exact Equiv.cast
    (congrArg (fun n => ZMod n × ZMod n)
      (fkRectBlackOrbitRibbonSubdivisionSide_eq_refinedProduct R))
    (fkRectRibbonSubdivisionCodeEmbed
      (8 * R.medialTorus.width) (8 * R.medialTorus.height)
      (fkRectBlackOrbitRibbonSubdivisionCode R omega d z))

end
end StatMech.FrontierD
