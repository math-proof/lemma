/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonSubdivisionIndexGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitRibbonSubdivisionCodeInjective
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectListFlatMapReplicate
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitRibbonSubdivisionIndexGeometry


namespace StatMech.FrontierD

open StatMech.Onsager

open StatMech.Onsager.BaseCase

noncomputable section

def fkRectBlackOrbitRibbonSubdivisionIndexEquiv
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    Fin (fkRectBlackOrbitRibbonSubdivisionWord R omega d).length ≃
      FKRectBlackOrbitRibbonSubdivisionIndex R omega d :=
  (finCongr
    (fkRectBlackOrbitRibbonSubdivisionWord_length_eq_sum R omega d)).trans
      finSigmaFinEquiv.symm

end
end StatMech.FrontierD
