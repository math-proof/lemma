/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleFibre.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourRowCycleBase.Part5
import Def.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourTwoCycleFibre.Part13


namespace StatMech.FrontierD

noncomputable section

set_option maxHeartbeats 4000000 in

set_option maxRecDepth 100000 in
theorem sixVertexFourByFourAuditedCoordinateRows_invariant
    (c : SixVertexFourByFourAuditedCoordinates) :
    SixVertexFourByFourAuditedCoordinateRowsInvariant c := by
  unfold SixVertexFourByFourAuditedCoordinateRowsInvariant
  rcases c with ⟨firstSeam, secondSeam, middle, last⟩
  fin_cases firstSeam <;> fin_cases secondSeam <;>
    fin_cases middle <;> fin_cases last <;> decide

theorem sixVertexFourByFour_iceRule_of_rowIce
    (omega : SixVertexArrows sixVertexFourByFourTorus)
    (hrow : forall y, svHorizontalIce sixVertexFourByFourTorus.width_pos
      (svTorusVerticalRows sixVertexFourByFourTorus omega
        (SixVertexArrows.cyclicPred sixVertexFourByFourTorus.height_pos y))
      (svTorusVerticalRows sixVertexFourByFourTorus omega y)
      (svTorusHorizontalRows sixVertexFourByFourTorus omega y)) :
    omega.IceRule := by
  intro v
  rcases v with ⟨x, y⟩
  simpa [svHorizontalIce, svHorizontalIncomingCount,
    svTorusVerticalRows, svTorusHorizontalRows,
    SixVertexArrows.incomingCount, Nat.add_assoc,
    Nat.add_left_comm, Nat.add_comm] using hrow y x

theorem sixVertexFourByFourAuditedCoordinateFirst_rowIce
    (c : SixVertexFourByFourAuditedCoordinates) (y : Fin 4) :
    let p := sixVertexFourByFourAuditedCoordinateParameters c
    svHorizontalIce sixVertexFourByFourTorus.width_pos
      (sixVertexFourByFourAuditedParamVerticalRowsFirst p c.firstSeam
        (SixVertexArrows.cyclicPred sixVertexFourByFourTorus.height_pos y))
      (sixVertexFourByFourAuditedParamVerticalRowsFirst p c.firstSeam y)
      (sixVertexFourByFourAuditedParamHorizontalRowsFirst p y) := by
  dsimp only
  let p := sixVertexFourByFourAuditedCoordinateParameters c
  have hinvariant := sixVertexFourByFourAuditedCoordinateRows_invariant c
  change SixVertexFourByFourAuditedCoordinateRowsInvariant c at hinvariant
  dsimp only [SixVertexFourByFourAuditedCoordinateRowsInvariant] at hinvariant
  rcases hinvariant with ⟨hfirst, _, hclose, _⟩
  change (forall y, sixVertexUpCount
      (sixVertexFourByFourAuditedParamVerticalRowsFirst p c.firstSeam y) = 1)
    at hfirst
  change sixVertexFourByFourAuditedParamVerticalRowsFirst p c.firstSeam 3 =
      sixVertexFourByFourRowOfMask
        (sixVertexFourByFourSectorOneSeamMask c.firstSeam) at hclose
  obtain ⟨i, hi⟩ :=
    sixVertexFourByFourAuditedParamHorizontalRowsFirst_allowed p y
  have hnext :
      sixVertexFourByFourAuditedParamVerticalRowsFirst p c.firstSeam y =
        sixVertexFourByFourNextVerticalRow
          (sixVertexFourByFourAuditedParamHorizontalRowsFirst p y)
          (sixVertexFourByFourAuditedParamVerticalRowsFirst p c.firstSeam
            (SixVertexArrows.cyclicPred sixVertexFourByFourTorus.height_pos y)) := by
    fin_cases y
    · change sixVertexFourByFourAuditedParamVerticalRowsFirst
          p c.firstSeam 0 =
        sixVertexFourByFourNextVerticalRow
          (sixVertexFourByFourAuditedParamHorizontalRowsFirst p 0)
          (sixVertexFourByFourAuditedParamVerticalRowsFirst p c.firstSeam 3)
      rw [hclose]
      rfl
    · rfl
    · rfl
    · rfl
  rw [hi] at hnext ⊢
  rw [hnext]
  apply sixVertexFourByFourNextVerticalRow_ice_of_upCount_eq i
  rw [← hnext, hfirst y, hfirst
      (SixVertexArrows.cyclicPred sixVertexFourByFourTorus.height_pos y)]

theorem sixVertexFourByFourAuditedCoordinateSecond_rowIce
    (c : SixVertexFourByFourAuditedCoordinates) (y : Fin 4) :
    let p := sixVertexFourByFourAuditedCoordinateParameters c
    svHorizontalIce sixVertexFourByFourTorus.width_pos
      (sixVertexFourByFourAuditedParamVerticalRowsSecond p c.secondSeam
        (SixVertexArrows.cyclicPred sixVertexFourByFourTorus.height_pos y))
      (sixVertexFourByFourAuditedParamVerticalRowsSecond p c.secondSeam y)
      (sixVertexFourByFourAuditedParamHorizontalRowsSecond p y) := by
  dsimp only
  let p := sixVertexFourByFourAuditedCoordinateParameters c
  have hinvariant := sixVertexFourByFourAuditedCoordinateRows_invariant c
  change SixVertexFourByFourAuditedCoordinateRowsInvariant c at hinvariant
  dsimp only [SixVertexFourByFourAuditedCoordinateRowsInvariant] at hinvariant
  rcases hinvariant with ⟨_, hsecond, _, hclose⟩
  change (forall y, sixVertexUpCount
      (sixVertexFourByFourAuditedParamVerticalRowsSecond p c.secondSeam y) = 3)
    at hsecond
  change sixVertexFourByFourAuditedParamVerticalRowsSecond p c.secondSeam 3 =
      sixVertexFourByFourRowOfMask
        (sixVertexFourByFourSectorThreeSeamMask c.secondSeam) at hclose
  obtain ⟨i, hi⟩ :=
    sixVertexFourByFourAuditedParamHorizontalRowsSecond_allowed p y
  have hnext :
      sixVertexFourByFourAuditedParamVerticalRowsSecond p c.secondSeam y =
        sixVertexFourByFourNextVerticalRow
          (sixVertexFourByFourAuditedParamHorizontalRowsSecond p y)
          (sixVertexFourByFourAuditedParamVerticalRowsSecond p c.secondSeam
            (SixVertexArrows.cyclicPred sixVertexFourByFourTorus.height_pos y)) := by
    fin_cases y
    · change sixVertexFourByFourAuditedParamVerticalRowsSecond
          p c.secondSeam 0 =
        sixVertexFourByFourNextVerticalRow
          (sixVertexFourByFourAuditedParamHorizontalRowsSecond p 0)
          (sixVertexFourByFourAuditedParamVerticalRowsSecond p c.secondSeam 3)
      rw [hclose]
      rfl
    · rfl
    · rfl
    · rfl
  rw [hi] at hnext ⊢
  rw [hnext]
  apply sixVertexFourByFourNextVerticalRow_ice_of_upCount_eq i
  rw [← hnext, hsecond y, hsecond
      (SixVertexArrows.cyclicPred sixVertexFourByFourTorus.height_pos y)]

theorem sixVertexFourByFourAuditedCoordinateSourcePair_valid
    (c : SixVertexFourByFourAuditedCoordinates) :
    SixVertexFourByFourAuditedCoordinateSourcePairValid c := by
  let p := sixVertexFourByFourAuditedCoordinateParameters c
  have hinvariant := sixVertexFourByFourAuditedCoordinateRows_invariant c
  change SixVertexFourByFourAuditedCoordinateRowsInvariant c at hinvariant
  dsimp only [SixVertexFourByFourAuditedCoordinateRowsInvariant] at hinvariant
  rcases hinvariant with ⟨hfirstCount, hsecondCount, _, _⟩
  unfold SixVertexFourByFourAuditedCoordinateSourcePairValid
  change (sixVertexFourByFourAuditedParamSourceFirst p c.firstSeam).IceRule /\
    (sixVertexFourByFourAuditedParamSourceSecond p c.secondSeam).IceRule /\ _ /\ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply sixVertexFourByFour_iceRule_of_rowIce
    intro y
    simpa [svTorusVerticalRows, svTorusHorizontalRows,
      sixVertexFourByFourAuditedParamSourceFirst] using
      sixVertexFourByFourAuditedCoordinateFirst_rowIce c y
  · apply sixVertexFourByFour_iceRule_of_rowIce
    intro y
    simpa [svTorusVerticalRows, svTorusHorizontalRows,
      sixVertexFourByFourAuditedParamSourceSecond] using
      sixVertexFourByFourAuditedCoordinateSecond_rowIce c y
  · simpa [svTorusVerticalRows,
      sixVertexFourByFourAuditedParamSourceFirst] using hfirstCount 3
  · simpa [svTorusVerticalRows,
      sixVertexFourByFourAuditedParamSourceSecond] using hsecondCount 3

end
end StatMech.FrontierD
