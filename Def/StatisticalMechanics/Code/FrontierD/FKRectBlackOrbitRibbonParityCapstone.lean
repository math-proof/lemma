/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonParityCapstone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitRibbonSubdivisionNonUturn


namespace StatMech.FrontierD

open StatMech.Onsager

open StatMech.Onsager.BaseCase

noncomputable section

def fkRectBlackOrbitFaithfulRibbonSubdivisionDart
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    Fin (fkRectBlackOrbitRibbonSubdivisionWord R omega d).length →
      ons_Dart (fkRectBlackOrbitRibbonSubdivisionSide R) :=
  fun k =>
    let z := fkRectBlackOrbitRibbonSubdivisionIndexEquiv R omega d (-k)
    (fkRectBlackOrbitRibbonSubdivisionSite R omega d z,
      fkRectBlackOrbitMedialRibbonFlatDirection R omega d z.1)

end
end StatMech.FrontierD
