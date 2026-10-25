/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourPhysicalBranch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourGradeCount
import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalParticleHole.Part4
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexVerticalRowsTotalC_le
    {T : EvenTorus} (vertical : Fin T.height → SixVertexRow T.width) :
    sixVertexVerticalRowsTotalC vertical ≤ T.height * T.width := by
  unfold sixVertexVerticalRowsTotalC
  calc
    _ ≤ ∑ _j : Fin T.height, T.width := by
      apply Finset.sum_le_sum
      intro j _
      exact sixVertexRowDistance_le_width _ _
    _ = _ := by simp [mul_comm]

theorem sixVertexMarkedSectorRowCycleGradeCount_eq_zero_of_area_lt
    (T : EvenTorus) (sector : Fin (T.width + 1)) (totalC : Nat)
    (hlarge : T.height * T.width < totalC) :
    sixVertexMarkedSectorRowCycleGradeCount T sector totalC = 0 := by
  unfold sixVertexMarkedSectorRowCycleGradeCount
  apply Finset.sum_eq_zero
  intro vertical _
  rw [if_neg]
  intro heq
  have hle := sixVertexVerticalRowsTotalC_le vertical.1
  omega

end
end StatMech.FrontierD
