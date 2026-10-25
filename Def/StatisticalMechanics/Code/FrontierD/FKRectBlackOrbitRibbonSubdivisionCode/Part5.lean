/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonSubdivisionCode.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitRibbonFlatGeometry
import Abbrev.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitRibbonSubdivisionCode


namespace StatMech.FrontierD

open StatMech.Onsager

open StatMech.Onsager.BaseCase

noncomputable section

def fkRectBlackOrbitRibbonSubdivisionCode
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus)
    (z : FKRectBlackOrbitRibbonSubdivisionIndex R omega d) :=
  fkRectRibbonSubdivisionCode
    (8 * R.medialTorus.width) (8 * R.medialTorus.height)
    (mul_pos (by decide) R.medialTorus.width_pos)
    (mul_pos (by decide) R.medialTorus.height_pos)
    (fkRectBlackOrbitMedialRibbonFlatSite R omega d z.1)
    (fkRectBlackOrbitMedialRibbonFlatDirection R omega d z.1) z.2

end
end StatMech.FrontierD
