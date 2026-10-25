/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitWindingGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnEssential
import Theorem.StatisticalMechanics.Code.Onsager.RectangularAxisSubdivision.Part8
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitWindingGeometry.Part9


namespace StatMech.FrontierD

open StatMech.Onsager

open StatMech.Onsager.BaseCase

noncomputable section

noncomputable def fkRectBlackOrbitSubdivisionDart
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    Fin (fkRectBlackOrbitShearSubdivisionWord R omega d).length →
      ons_Dart (fkRectBlackOrbitSubdivisionSide R) := by
  let word := fkRectBlackOrbitShearSubdivisionWord R omega d
  have hword : word ≠ [] :=
    fkRectBlackOrbitShearSubdivisionWord_nonempty R omega d
  letI : NeZero word.length :=
    ⟨(List.length_pos_iff_ne_nil.mpr hword).ne'⟩
  exact onsDirectionWordTorusDart
    (fkRectBlackOrbitSubdivisionSide R) word

end
end StatMech.FrontierD
