/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitWindingGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnEssential
import Theorem.StatisticalMechanics.Code.Onsager.RectangularAxisSubdivision.Part8
import Def.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitWindingGeometry.Part6


namespace StatMech.FrontierD

open StatMech.Onsager

open StatMech.Onsager.BaseCase

noncomputable section

theorem fkRectBlackOrbitShearSubdivisionWord_nonempty
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    fkRectBlackOrbitShearSubdivisionWord R omega d ≠ [] := by
  let pairing := fkRectConfigurationToMedialPairing R omega
  let dir := fkRectBlackOrbitDirection pairing d
  let original := List.ofFn dir
  have hn : 0 < (fkRectBlackOrbitList pairing d).length :=
    fkRectBlackOrbitList_length_pos pairing d
  letI : NeZero (fkRectBlackOrbitList pairing d).length := ⟨hn.ne'⟩
  have horiginal : original ≠ [] := by simp [original, NeZero.ne _]
  have hshear : onsDiagonalShearDirectionWord original ≠ [] := by
    intro hnil
    rw [onsDiagonalShearDirectionWord, List.flatMap_eq_nil_iff] at hnil
    have hmem : dir 0 ∈ original := by
      rw [List.mem_ofFn]
      exact ⟨0, rfl⟩
    have := hnil (dir 0) hmem
    generalize hdir : dir 0 = a at this
    fin_cases a <;>
      simp [onsDiagonalShearDirectionBlock] at this
  intro hnil
  change onsAnisotropicDirectionWord (4 * R.width) (2 * R.height)
      (onsDiagonalShearDirectionWord original) = [] at hnil
  rw [onsAnisotropicDirectionWord, List.flatMap_eq_nil_iff] at hnil
  obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil
    (onsDiagonalShearDirectionWord original) hshear
  have hzero := (List.replicate_eq_nil_iff a).mp (hnil a ha)
  have hpos : 0 < onsAnisotropicStepScale
      (4 * R.width) (2 * R.height) a := by
    fin_cases a <;>
      simp [onsAnisotropicStepScale, R.width_pos, R.height_pos]
  omega

end
end StatMech.FrontierD
