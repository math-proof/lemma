/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourPhysicalBranch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourGradeCount
import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalParticleHole.Part4
import Def.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourPhysicalBranch.Part4
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFourByFourOffDiagonalGradeCount_eq_nat
    (sector : Fin 5) (totalC : Nat) :
    Nat.card
        {target : SixVertexPhysicalRowCycleOffDiagonalTarget
            sixVertexFourByFourTorus sector //
          sixVertexPhysicalRowCyclePairTotalC target.1 = totalC} =
      sixVertexFourByFourOffDiagonalGradeCountNat sector totalC := by
  have hcard :
      Nat.card
          {target : SixVertexPhysicalRowCycleOffDiagonalTarget
              sixVertexFourByFourTorus sector //
            sixVertexPhysicalRowCyclePairTotalC target.1 = totalC} =
        sixVertexMarkedSectorRowCyclePairGradeCount
            sixVertexFourByFourTorus sector sector totalC -
          sixVertexMarkedSectorRowCycleDiagonalGradeCount
            sixVertexFourByFourTorus sector totalC := by
    simpa only [← Nat.card_eq_fintype_card] using
      card_sixVertexPhysicalRowCycleOffDiagonalGradeFiber
        sixVertexFourByFourTorus sector totalC
  rw [hcard]
  unfold sixVertexFourByFourOffDiagonalGradeCountNat
  rw [sixVertexFourByFourRowCyclePairGradeCount_eq_nat,
    sixVertexFourByFourDiagonalGradeCount_eq_nat]

set_option maxHeartbeats 1000000 in

theorem sixVertexFourByFour_middleOne_gradeCapacity_certificate :
    ∀ totalC : Fin 33,
      sixVertexFourByFourPairGradeCountNat 0 2 totalC.val ≤
        sixVertexFourByFourOffDiagonalGradeCountNat 1 totalC.val := by
  decide +revert

set_option maxHeartbeats 1000000 in

theorem sixVertexFourByFour_middleTwo_gradeCapacity_certificate :
    ∀ totalC : Fin 33,
      sixVertexFourByFourPairGradeCountNat 1 3 totalC.val ≤
        sixVertexFourByFourOffDiagonalGradeCountNat 2 totalC.val := by
  decide +revert

theorem sixVertexFourByFourSectorOne_pos :
    0 < sixVertexFourByFourSectorOne.val := by
  norm_num [sixVertexFourByFourSectorOne]

theorem sixVertexFourByFourSectorOne_lt_width :
    sixVertexFourByFourSectorOne.val < sixVertexFourByFourTorus.width := by
  norm_num [sixVertexFourByFourSectorOne, sixVertexFourByFourTorus]

theorem sixVertexFourByFourSectorTwo_pos :
    0 < sixVertexFourByFourSectorTwo.val := by
  norm_num [sixVertexFourByFourSectorTwo]

theorem sixVertexFourByFourSectorTwo_lt_width :
    sixVertexFourByFourSectorTwo.val < sixVertexFourByFourTorus.width := by
  norm_num [sixVertexFourByFourSectorTwo, sixVertexFourByFourTorus]

theorem sixVertexFourByFourPhysicalSourceGradeCount_middleOne
    (totalC : Nat) :
    Nat.card
        {source : SixVertexPhysicalRowCycleSource sixVertexFourByFourTorus
            sixVertexFourByFourSectorOne
            sixVertexFourByFourSectorOne_pos
            sixVertexFourByFourSectorOne_lt_width //
          sixVertexPhysicalRowCyclePairTotalC source = totalC} =
      sixVertexFourByFourPairGradeCountNat 0 2 totalC := by
  change Nat.card
      {source : SixVertexMarkedSectorRowCycle sixVertexFourByFourTorus 0 ×
          SixVertexMarkedSectorRowCycle sixVertexFourByFourTorus 2 //
        sixVertexMarkedSectorRowCyclePairTotalC source = totalC} = _
  rw [Nat.card_eq_fintype_card,
    card_sixVertexMarkedSectorRowCyclePairGradeFiber,
    sixVertexFourByFourRowCyclePairGradeCount_eq_nat]
  rfl

theorem sixVertexFourByFourPhysicalSourceGradeCount_middleTwo
    (totalC : Nat) :
    Nat.card
        {source : SixVertexPhysicalRowCycleSource sixVertexFourByFourTorus
            sixVertexFourByFourSectorTwo
            sixVertexFourByFourSectorTwo_pos
            sixVertexFourByFourSectorTwo_lt_width //
          sixVertexPhysicalRowCyclePairTotalC source = totalC} =
      sixVertexFourByFourPairGradeCountNat 1 3 totalC := by
  change Nat.card
      {source : SixVertexMarkedSectorRowCycle sixVertexFourByFourTorus 1 ×
          SixVertexMarkedSectorRowCycle sixVertexFourByFourTorus 3 //
        sixVertexMarkedSectorRowCyclePairTotalC source = totalC} = _
  rw [Nat.card_eq_fintype_card,
    card_sixVertexMarkedSectorRowCyclePairGradeFiber,
    sixVertexFourByFourRowCyclePairGradeCount_eq_nat]
  rfl

theorem sixVertexFourByFourRowCycleTotalC_le
    {sector : Fin 5}
    (rows : SixVertexMarkedSectorRowCycle sixVertexFourByFourTorus sector) :
    sixVertexMarkedSectorRowCycleTotalC rows ≤ 16 := by
  change sixVertexVerticalRowsTotalC rows.1.2 ≤ 16
  simpa [sixVertexFourByFourTorus] using
    sixVertexVerticalRowsTotalC_le rows.1.2

theorem sixVertexFourByFourPhysicalSourceTotalC_le
    {middle : Fin 5} {hmiddle_pos : 0 < middle.val}
    {hmiddle_lt : middle.val < sixVertexFourByFourTorus.width}
    (source : SixVertexPhysicalRowCycleSource sixVertexFourByFourTorus
      middle hmiddle_pos hmiddle_lt) :
    sixVertexPhysicalRowCyclePairTotalC source ≤ 32 := by
  change sixVertexMarkedSectorRowCycleTotalC source.1 +
    sixVertexMarkedSectorRowCycleTotalC source.2 ≤ 32
  have hleft := sixVertexFourByFourRowCycleTotalC_le source.1
  have hright := sixVertexFourByFourRowCycleTotalC_le source.2
  omega

theorem sixVertexFourByFourMiddleOneExactGradeCapacity :
    SixVertexPhysicalRowCycleExactGradeCapacity sixVertexFourByFourTorus
      sixVertexFourByFourSectorOne
      sixVertexFourByFourSectorOne_pos
      sixVertexFourByFourSectorOne_lt_width := by
  intro totalC
  apply Function.Embedding.nonempty_of_card_le
  simp only [← Nat.card_eq_fintype_card]
  rw [sixVertexFourByFourPhysicalSourceGradeCount_middleOne,
    sixVertexFourByFourOffDiagonalGradeCount_eq_nat]
  by_cases htotal : totalC < 33
  · exact sixVertexFourByFour_middleOne_gradeCapacity_certificate
      ⟨totalC, htotal⟩
  · have hzero : sixVertexFourByFourPairGradeCountNat 0 2 totalC = 0 := by
      rw [← sixVertexFourByFourPhysicalSourceGradeCount_middleOne]
      apply Nat.card_eq_zero.mpr
      left
      constructor
      intro source
      have hle := sixVertexFourByFourPhysicalSourceTotalC_le source.1
      omega
    simp [hzero]

theorem sixVertexFourByFourMiddleTwoExactGradeCapacity :
    SixVertexPhysicalRowCycleExactGradeCapacity sixVertexFourByFourTorus
      sixVertexFourByFourSectorTwo
      sixVertexFourByFourSectorTwo_pos
      sixVertexFourByFourSectorTwo_lt_width := by
  intro totalC
  apply Function.Embedding.nonempty_of_card_le
  simp only [← Nat.card_eq_fintype_card]
  rw [sixVertexFourByFourPhysicalSourceGradeCount_middleTwo,
    sixVertexFourByFourOffDiagonalGradeCount_eq_nat]
  by_cases htotal : totalC < 33
  · exact sixVertexFourByFour_middleTwo_gradeCapacity_certificate
      ⟨totalC, htotal⟩
  · have hzero : sixVertexFourByFourPairGradeCountNat 1 3 totalC = 0 := by
      rw [← sixVertexFourByFourPhysicalSourceGradeCount_middleTwo]
      apply Nat.card_eq_zero.mpr
      left
      constructor
      intro source
      have hle := sixVertexFourByFourPhysicalSourceTotalC_le source.1
      omega
    simp [hzero]

end
end StatMech.FrontierD
