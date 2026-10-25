/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitWindingGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnEssential
import Theorem.StatisticalMechanics.Code.Onsager.RectangularAxisSubdivision.Part8
import Def.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitWindingGeometry.Part4


namespace StatMech.FrontierD

open StatMech.Onsager

open StatMech.Onsager.BaseCase

noncomputable section

theorem fkRectBlackOrbitRibbonSubdivisionSide_gt_two (R : FKRectTorus) :
    2 < fkRectBlackOrbitRibbonSubdivisionSide R := by
  unfold fkRectBlackOrbitRibbonSubdivisionSide
  nlinarith [R.width_pos, R.height_pos]

theorem fkRectBlackOrbitRibbonSubdivisionWord_nonempty
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    fkRectBlackOrbitRibbonSubdivisionWord R omega d ≠ [] := by
  let word := fkRectBlackOrbitMedialRibbonWord R omega d
  have hword : word ≠ [] :=
    fkRectBlackOrbitMedialRibbonWord_nonempty R omega d
  intro hnil
  change onsAnisotropicDirectionWord
      (16 * R.width) (8 * R.height) word = [] at hnil
  rw [onsAnisotropicDirectionWord, List.flatMap_eq_nil_iff] at hnil
  obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil word hword
  have hzero := (List.replicate_eq_nil_iff a).mp (hnil a ha)
  have hpos : 0 < onsAnisotropicStepScale
      (16 * R.width) (8 * R.height) a := by
    fin_cases a <;>
      simp [onsAnisotropicStepScale, R.width_pos, R.height_pos]
  omega

end
end StatMech.FrontierD
