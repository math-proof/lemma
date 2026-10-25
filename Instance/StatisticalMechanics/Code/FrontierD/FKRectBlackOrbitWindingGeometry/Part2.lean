/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitWindingGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnEssential
import Theorem.StatisticalMechanics.Code.Onsager.RectangularAxisSubdivision.Part8
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitWindingGeometry.Part7


namespace StatMech.FrontierD

open StatMech.Onsager

open StatMech.Onsager.BaseCase

noncomputable section

instance fkRectBlackOrbitShearSubdivisionWord_length_neZero
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    NeZero (fkRectBlackOrbitShearSubdivisionWord R omega d).length :=
  ⟨(List.length_pos_iff_ne_nil.mpr
    (fkRectBlackOrbitShearSubdivisionWord_nonempty R omega d)).ne'⟩


end
end StatMech.FrontierD
