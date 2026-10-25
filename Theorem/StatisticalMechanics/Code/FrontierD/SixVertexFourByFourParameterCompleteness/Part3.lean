/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourParameterCompleteness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourRowAutomaton.Part4
import Def.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourParameterCompleteness.Part2


namespace StatMech.FrontierD

theorem sixVertexFourByFourAudited_firstMiddlePath_of_valid
    (p : SixVertexFourByFourAuditedHorizontalParameters)
    (firstSeam secondSeam : Fin 4)
    (hrowZero : sixVertexFourByFourAuditedCoordinateRowZero
      firstSeam secondSeam = p.1)
    (hice : (sixVertexFourByFourAuditedParamSourceFirst p firstSeam).IceRule)
    (hsector : sixVertexUpCount
      (svTorusVerticalRows sixVertexFourByFourTorus
        (sixVertexFourByFourAuditedParamSourceFirst p firstSeam)
        (svFinLast sixVertexFourByFourTorus.height_pos)) = 1) :
    (sixVertexFourByFourAuditedFirstTransition
          (sixVertexFourByFourAuditedOppositeSeam firstSeam) p.2.1 >>= fun s =>
        sixVertexFourByFourAuditedFirstTransition s p.2.2.1) =
      some firstSeam := by
  let rows := sixVertexFourByFourAuditedParamVerticalRowsFirst p firstSeam
  have hcount (y : Fin 4) : sixVertexUpCount (rows y) = 1 := by
    exact sixVertexFourByFourAuditedParamSourceFirst_verticalRowCount
      p firstSeam y hice hsector
  have hdecodeZero :
      sixVertexFourByFourAuditedFirstStateDecode (rows 0) =
        some (sixVertexFourByFourAuditedOppositeSeam firstSeam) := by
    simpa [rows, sixVertexFourByFourAuditedParamVerticalRowsFirst,
      sixVertexFourByFourAuditedParamHorizontalRowsFirst, hrowZero] using
      sixVertexFourByFourAudited_firstRowZero_opposite firstSeam secondSeam
  have hrowZeroState := sixVertexFourByFourAudited_firstRow_eq_of_decode _ _ hdecodeZero
  obtain ⟨stateOne, hdecodeOne⟩ :=
    sixVertexFourByFourAudited_firstDecode_exists_of_count (rows 1) (hcount 1)
  obtain ⟨stateTwo, hdecodeTwo⟩ :=
    sixVertexFourByFourAudited_firstDecode_exists_of_count (rows 2) (hcount 2)
  obtain ⟨stateThree, hdecodeThree⟩ :=
    sixVertexFourByFourAudited_firstDecode_exists_of_count (rows 3) (hcount 3)
  have hrowOneState := sixVertexFourByFourAudited_firstRow_eq_of_decode _ _ hdecodeOne
  have hrowTwoState := sixVertexFourByFourAudited_firstRow_eq_of_decode _ _ hdecodeTwo
  have hrowThreeState := sixVertexFourByFourAudited_firstRow_eq_of_decode _ _ hdecodeThree
  have htransitionOne :
      sixVertexFourByFourAuditedFirstTransition
          (sixVertexFourByFourAuditedOppositeSeam firstSeam) p.2.1 =
        some stateOne := by
    unfold sixVertexFourByFourAuditedFirstTransition
    rw [← hrowZeroState]
    simpa [rows, sixVertexFourByFourAuditedParamVerticalRowsFirst,
      sixVertexFourByFourAuditedParamHorizontalRowsFirst,
      sixVertexFourByFourAuditedFirstMiddleRow] using hdecodeOne
  have htransitionTwo :
      sixVertexFourByFourAuditedFirstTransition stateOne p.2.2.1 =
        some stateTwo := by
    unfold sixVertexFourByFourAuditedFirstTransition
    rw [← hrowOneState]
    simpa [rows, sixVertexFourByFourAuditedParamVerticalRowsFirst,
      sixVertexFourByFourAuditedParamHorizontalRowsFirst,
      sixVertexFourByFourAuditedFirstMiddleRow] using hdecodeTwo
  have hrowIceZero := sixVertexFourByFour_rowIce
    (sixVertexFourByFourAuditedParamSourceFirst p firstSeam) hice 0
  change svHorizontalIce sixVertexFourByFourTorus.width_pos
      (rows 3) (rows 0)
      (sixVertexFourByFourAuditedParamHorizontalRowsFirst p 0) at hrowIceZero
  have hnextZero := sixVertexFourByFourAudited_nextVerticalRow_eq_of_ice
    (rows 3) (rows 0)
      (sixVertexFourByFourAuditedParamHorizontalRowsFirst p 0) hrowIceZero
  have hrowZeroReverse :
      sixVertexFourByFourAuditedFirstStateDecode
          (sixVertexFourByFourNextVerticalRow
            (sixVertexFourByFourRowOfMask
              (sixVertexFourByFourAuditedRowZero
                (sixVertexFourByFourAuditedCoordinateRowZero
                  firstSeam secondSeam)).1)
            (sixVertexFourByFourAuditedFirstStateRow stateThree)) =
        some (sixVertexFourByFourAuditedOppositeSeam firstSeam) := by
    rw [← hrowThreeState]
    have hdecodeNext := congrArg
      sixVertexFourByFourAuditedFirstStateDecode hnextZero
    rw [hdecodeZero] at hdecodeNext
    simpa [sixVertexFourByFourAuditedParamHorizontalRowsFirst,
      hrowZero] using hdecodeNext
  have hstateThree : stateThree = firstSeam :=
    (sixVertexFourByFourAudited_firstRowZero_reverse firstSeam secondSeam stateThree).mp
      hrowZeroReverse
  have hlast := sixVertexFourByFourAudited_firstVerticalRow_three_eq_two p firstSeam
  have hstateTwoThree : stateTwo = stateThree := by
    have hdecodeLast := congrArg
      sixVertexFourByFourAuditedFirstStateDecode hlast
    change rows 3 = rows 2 at hlast
    rw [hdecodeThree, hdecodeTwo] at hdecodeLast
    exact (Option.some.inj hdecodeLast).symm
  rw [htransitionOne]
  change sixVertexFourByFourAuditedFirstTransition stateOne p.2.2.1 =
    some firstSeam
  rw [htransitionTwo]
  exact congrArg some (hstateTwoThree.trans hstateThree)

theorem sixVertexFourByFourAudited_secondMiddlePath_of_valid
    (p : SixVertexFourByFourAuditedHorizontalParameters)
    (firstSeam secondSeam : Fin 4)
    (hrowZero : sixVertexFourByFourAuditedCoordinateRowZero
      firstSeam secondSeam = p.1)
    (hice : (sixVertexFourByFourAuditedParamSourceSecond p secondSeam).IceRule)
    (hsector : sixVertexUpCount
      (svTorusVerticalRows sixVertexFourByFourTorus
        (sixVertexFourByFourAuditedParamSourceSecond p secondSeam)
        (svFinLast sixVertexFourByFourTorus.height_pos)) = 3) :
    (sixVertexFourByFourAuditedSecondTransition
          (sixVertexFourByFourAuditedOppositeSeam secondSeam) p.2.1 >>= fun s =>
        sixVertexFourByFourAuditedSecondTransition s p.2.2.1) =
      some secondSeam := by
  let rows := sixVertexFourByFourAuditedParamVerticalRowsSecond p secondSeam
  have hcount (y : Fin 4) : sixVertexUpCount (rows y) = 3 := by
    exact sixVertexFourByFourAuditedParamSourceSecond_verticalRowCount
      p secondSeam y hice hsector
  have hdecodeZero :
      sixVertexFourByFourAuditedSecondStateDecode (rows 0) =
        some (sixVertexFourByFourAuditedOppositeSeam secondSeam) := by
    simpa [rows, sixVertexFourByFourAuditedParamVerticalRowsSecond,
      sixVertexFourByFourAuditedParamHorizontalRowsSecond, hrowZero] using
      sixVertexFourByFourAudited_secondRowZero_opposite firstSeam secondSeam
  have hrowZeroState := sixVertexFourByFourAudited_secondRow_eq_of_decode _ _ hdecodeZero
  obtain ⟨stateOne, hdecodeOne⟩ :=
    sixVertexFourByFourAudited_secondDecode_exists_of_count (rows 1) (hcount 1)
  obtain ⟨stateTwo, hdecodeTwo⟩ :=
    sixVertexFourByFourAudited_secondDecode_exists_of_count (rows 2) (hcount 2)
  obtain ⟨stateThree, hdecodeThree⟩ :=
    sixVertexFourByFourAudited_secondDecode_exists_of_count (rows 3) (hcount 3)
  have hrowOneState := sixVertexFourByFourAudited_secondRow_eq_of_decode _ _ hdecodeOne
  have hrowTwoState := sixVertexFourByFourAudited_secondRow_eq_of_decode _ _ hdecodeTwo
  have hrowThreeState := sixVertexFourByFourAudited_secondRow_eq_of_decode _ _ hdecodeThree
  have htransitionOne :
      sixVertexFourByFourAuditedSecondTransition
          (sixVertexFourByFourAuditedOppositeSeam secondSeam) p.2.1 =
        some stateOne := by
    unfold sixVertexFourByFourAuditedSecondTransition
    rw [← hrowZeroState]
    simpa [rows, sixVertexFourByFourAuditedParamVerticalRowsSecond,
      sixVertexFourByFourAuditedParamHorizontalRowsSecond,
      sixVertexFourByFourAuditedSecondMiddleRow] using hdecodeOne
  have htransitionTwo :
      sixVertexFourByFourAuditedSecondTransition stateOne p.2.2.1 =
        some stateTwo := by
    unfold sixVertexFourByFourAuditedSecondTransition
    rw [← hrowOneState]
    simpa [rows, sixVertexFourByFourAuditedParamVerticalRowsSecond,
      sixVertexFourByFourAuditedParamHorizontalRowsSecond,
      sixVertexFourByFourAuditedSecondMiddleRow] using hdecodeTwo
  have hrowIceZero := sixVertexFourByFour_rowIce
    (sixVertexFourByFourAuditedParamSourceSecond p secondSeam) hice 0
  change svHorizontalIce sixVertexFourByFourTorus.width_pos
      (rows 3) (rows 0)
      (sixVertexFourByFourAuditedParamHorizontalRowsSecond p 0) at hrowIceZero
  have hnextZero := sixVertexFourByFourAudited_nextVerticalRow_eq_of_ice
    (rows 3) (rows 0)
      (sixVertexFourByFourAuditedParamHorizontalRowsSecond p 0) hrowIceZero
  have hrowZeroReverse :
      sixVertexFourByFourAuditedSecondStateDecode
          (sixVertexFourByFourNextVerticalRow
            (sixVertexFourByFourRowOfMask
              (sixVertexFourByFourAuditedRowZero
                (sixVertexFourByFourAuditedCoordinateRowZero
                  firstSeam secondSeam)).2)
            (sixVertexFourByFourAuditedSecondStateRow stateThree)) =
        some (sixVertexFourByFourAuditedOppositeSeam secondSeam) := by
    rw [← hrowThreeState]
    have hdecodeNext := congrArg
      sixVertexFourByFourAuditedSecondStateDecode hnextZero
    rw [hdecodeZero] at hdecodeNext
    simpa [sixVertexFourByFourAuditedParamHorizontalRowsSecond,
      hrowZero] using hdecodeNext
  have hstateThree : stateThree = secondSeam :=
    (sixVertexFourByFourAudited_secondRowZero_reverse firstSeam secondSeam stateThree).mp
      hrowZeroReverse
  have hlast := sixVertexFourByFourAudited_secondVerticalRow_three_eq_two p secondSeam
  have hstateTwoThree : stateTwo = stateThree := by
    have hdecodeLast := congrArg
      sixVertexFourByFourAuditedSecondStateDecode hlast
    change rows 3 = rows 2 at hlast
    rw [hdecodeThree, hdecodeTwo] at hdecodeLast
    exact (Option.some.inj hdecodeLast).symm
  rw [htransitionOne]
  change sixVertexFourByFourAuditedSecondTransition stateOne p.2.2.1 =
    some secondSeam
  rw [htransitionTwo]
  exact congrArg some (hstateTwoThree.trans hstateThree)

theorem sixVertexFourByFourAudited_parameterValid_uniqueCoordinate
    (p : SixVertexFourByFourAuditedHorizontalParameters)
    (hvalid : SixVertexFourByFourAuditedParameterValid p) :
    ∃! c : SixVertexFourByFourAuditedCoordinates,
      sixVertexFourByFourAuditedCoordinateParameters c = p := by
  let seams := sixVertexFourByFourAuditedDecodedSeams p.1
  have hrowZero : sixVertexFourByFourAuditedCoordinateRowZero
      seams.1 seams.2 = p.1 := by
    exact sixVertexFourByFourAudited_decodedSeams_inverse p.1
  unfold SixVertexFourByFourAuditedParameterValid sixVertexFourByFourAuditedParameterSourcePair at hvalid
  dsimp only at hvalid
  have hfirstPath := sixVertexFourByFourAudited_firstMiddlePath_of_valid
    p seams.1 seams.2 hrowZero hvalid.1 hvalid.2.2.1
  have hsecondPath := sixVertexFourByFourAudited_secondMiddlePath_of_valid
    p seams.1 seams.2 hrowZero hvalid.2.1 hvalid.2.2.2
  have hpath : sixVertexFourByFourAuditedMiddlePathAllowed
      seams.1 seams.2 p.2.1 p.2.2.1 := ⟨hfirstPath, hsecondPath⟩
  obtain ⟨middle, hmiddle⟩ :=
    (sixVertexFourByFourAudited_middlePathAllowed_iff_template
      seams.1 seams.2 p.2.1 p.2.2.1).mp hpath
  let c : SixVertexFourByFourAuditedCoordinates :=
    ⟨seams.1, seams.2, middle, p.2.2.2⟩
  have hc : sixVertexFourByFourAuditedCoordinateParameters c = p := by
    unfold sixVertexFourByFourAuditedCoordinateParameters c
    dsimp only
    apply Prod.ext
    · exact hrowZero
    · apply Prod.ext
      · change (sixVertexFourByFourAuditedMiddlePair
            seams.1 seams.2 middle).1 = p.2.1
        exact congrArg Prod.fst hmiddle.symm
      · apply Prod.ext
        · change (sixVertexFourByFourAuditedMiddlePair
              seams.1 seams.2 middle).2 = p.2.2.1
          exact congrArg Prod.snd hmiddle.symm
        · rfl
  refine ⟨c, hc, ?_⟩
  intro other hother
  exact sixVertexFourByFourAuditedCoordinateParameters_injective
    (hother.trans hc.symm)

theorem sixVertexFourByFourAudited_decodedSeams_coordinateRowZero
    (firstSeam secondSeam : Fin 4) :
    sixVertexFourByFourAuditedDecodedSeams
        (sixVertexFourByFourAuditedCoordinateRowZero firstSeam secondSeam) =
      (firstSeam, secondSeam) := by
  fin_cases firstSeam <;> fin_cases secondSeam <;> decide

theorem sixVertexFourByFourAudited_coordinateParameters_valid
    (c : SixVertexFourByFourAuditedCoordinates) :
    SixVertexFourByFourAuditedParameterValid
      (sixVertexFourByFourAuditedCoordinateParameters c) := by
  have hsource := sixVertexFourByFourAuditedCoordinateSourcePair_valid c
  simpa [SixVertexFourByFourAuditedParameterValid,
    sixVertexFourByFourAuditedParameterSourcePair,
    sixVertexFourByFourAuditedCoordinateSourcePair,
    sixVertexFourByFourAuditedCoordinateParameters,
    sixVertexFourByFourAudited_decodedSeams_coordinateRowZero] using hsource

end StatMech.FrontierD
