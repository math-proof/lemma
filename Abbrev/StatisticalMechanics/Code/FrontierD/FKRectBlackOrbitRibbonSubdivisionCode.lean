/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonSubdivisionCode.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitRibbonFlatGeometry
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitRibbonSubdivisionCode.Part4


namespace StatMech.FrontierD

open StatMech.Onsager

open StatMech.Onsager.BaseCase

noncomputable section

abbrev FKRectBlackOrbitRibbonSubdivisionIndex
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :=
  Σ k : Fin (fkRectBlackOrbitMedialRibbonWord R omega d).length,
    Fin (onsAnisotropicStepScale (8 * R.medialTorus.width)
      (8 * R.medialTorus.height)
      (fkRectBlackOrbitMedialRibbonFlatDirection R omega d k))

end
end StatMech.FrontierD
