/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourPhysicalBranch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourGradeCount
import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalParticleHole.Part4
import Def.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourPhysicalBranch.Part2
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFourByFourRowCyclePairGradeCount_eq_nat
    (left right : Fin 5) (totalC : Nat) :
    sixVertexMarkedSectorRowCyclePairGradeCount
        sixVertexFourByFourTorus left right totalC =
      sixVertexFourByFourPairGradeCountNat left right totalC := by
  rw [sixVertexMarkedSectorRowCyclePairGradeCount_eq_convolution]
  unfold sixVertexFourByFourPairGradeCountNat
  apply Finset.sum_congr rfl
  intro grade _
  rw [sixVertexFourByFourRowCycleGradeCount_eq_nat,
    sixVertexFourByFourRowCycleGradeCount_eq_nat]

theorem sixVertexMarkedSectorRowCycleDiagonalGradeCount_eq_nat
    (T : EvenTorus) (sector : Fin (T.width + 1)) (totalC : Nat) :
    sixVertexMarkedSectorRowCycleDiagonalGradeCount T sector totalC =
      if totalC % 2 = 0 then
        sixVertexMarkedSectorRowCycleGradeCount T sector (totalC / 2)
      else 0 := by
  unfold sixVertexMarkedSectorRowCycleDiagonalGradeCount
    sixVertexMarkedSectorRowCycleGradeCount
  by_cases heven : totalC % 2 = 0
  · rw [if_pos heven]
    apply Finset.sum_congr rfl
    intro vertical _
    apply if_congr
    · constructor <;> intro h <;> omega
    · rfl
    · rfl
  · rw [if_neg heven]
    apply Finset.sum_eq_zero
    intro vertical _
    rw [if_neg]
    intro hgrade
    have : totalC % 2 = 0 := by omega
    exact heven this

end
end StatMech.FrontierD
