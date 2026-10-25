import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourParameterCompleteness.Part6
open StatMech StatMech.FrontierD


/--
[sixVertexFourByFourAudited_rowOfBits_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourParameterCompleteness.lean)
-/
@[path]
private lemma sixVertexFourByFourAudited_rowOfBits_injective_eq :
-- imply
  Function.Injective (Nat.ofBits : SixVertexRow 4 -> Nat) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAudited_rowOfBits_injective

/--
[sixVertexFourByFourAudited_firstRowZero_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourParameterCompleteness.lean)
-/
@[path]
private lemma sixVertexFourByFourAudited_firstRowZero_reverse_eq
  {firstSeam secondSeam state : Fin 4} :
-- imply
  sixVertexFourByFourAuditedFirstStateDecode (sixVertexFourByFourNextVerticalRow (sixVertexFourByFourRowOfMask (sixVertexFourByFourAuditedRowZero (sixVertexFourByFourAuditedCoordinateRowZero firstSeam secondSeam)).1) (sixVertexFourByFourAuditedFirstStateRow state)) = some (sixVertexFourByFourAuditedOppositeSeam firstSeam) <-> state = firstSeam := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAudited_firstRowZero_reverse firstSeam secondSeam state

/--
[sixVertexFourByFourAudited_secondRowZero_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourParameterCompleteness.lean)
-/
@[path]
private lemma sixVertexFourByFourAudited_secondRowZero_reverse_eq
  {firstSeam secondSeam state : Fin 4} :
-- imply
  sixVertexFourByFourAuditedSecondStateDecode (sixVertexFourByFourNextVerticalRow (sixVertexFourByFourRowOfMask (sixVertexFourByFourAuditedRowZero (sixVertexFourByFourAuditedCoordinateRowZero firstSeam secondSeam)).2) (sixVertexFourByFourAuditedSecondStateRow state)) = some (sixVertexFourByFourAuditedOppositeSeam secondSeam) <-> state = secondSeam := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAudited_secondRowZero_reverse firstSeam secondSeam state

/--
[sixVertexFourByFourAudited_nextVerticalRow_constant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourParameterCompleteness.lean)
-/
@[path]
private lemma sixVertexFourByFourAudited_nextVerticalRow_constant_eq
  {value : Bool}
  {below : SixVertexRow 4} :
-- imply
  sixVertexFourByFourNextVerticalRow (fun _ => value) below = below := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAudited_nextVerticalRow_constant value below

/--
[sixVertexFourByFourAudited_decodedSeams_inverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourParameterCompleteness.lean)
-/
@[path]
private lemma sixVertexFourByFourAudited_decodedSeams_inverse_eq
  {rowZero : Fin 16} :
-- imply
  sixVertexFourByFourAuditedCoordinateRowZero (sixVertexFourByFourAuditedDecodedSeams rowZero).1 (sixVertexFourByFourAuditedDecodedSeams rowZero).2 = rowZero := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAudited_decodedSeams_inverse rowZero

/--
[sixVertexFourByFourAudited_firstDecode_exists_of_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourParameterCompleteness.lean)
-/
@[path]
private lemma sixVertexFourByFourAudited_firstDecode_exists_of_count_eq
  {row : SixVertexRow 4}
-- given
  (hcount : sixVertexUpCount row = 1) :
-- imply
  exists state, sixVertexFourByFourAuditedFirstStateDecode row = some state := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAudited_firstDecode_exists_of_count row hcount

/--
[sixVertexFourByFourAudited_secondDecode_exists_of_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourParameterCompleteness.lean)
-/
@[path]
private lemma sixVertexFourByFourAudited_secondDecode_exists_of_count_eq
  {row : SixVertexRow 4}
-- given
  (hcount : sixVertexUpCount row = 3) :
-- imply
  exists state, sixVertexFourByFourAuditedSecondStateDecode row = some state := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAudited_secondDecode_exists_of_count row hcount

/--
[sixVertexFourByFourAudited_firstRow_eq_of_decode](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourParameterCompleteness.lean)
-/
@[path]
private lemma sixVertexFourByFourAudited_firstRow_eq_of_decode_eq
  {row : SixVertexRow 4}
  {state : Fin 4}
-- given
  (hdecode : sixVertexFourByFourAuditedFirstStateDecode row = some state) :
-- imply
  row = sixVertexFourByFourAuditedFirstStateRow state := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAudited_firstRow_eq_of_decode row state hdecode

/--
[sixVertexFourByFourAudited_secondRow_eq_of_decode](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourParameterCompleteness.lean)
-/
@[path]
private lemma sixVertexFourByFourAudited_secondRow_eq_of_decode_eq
  {row : SixVertexRow 4}
  {state : Fin 4}
-- given
  (hdecode : sixVertexFourByFourAuditedSecondStateDecode row = some state) :
-- imply
  row = sixVertexFourByFourAuditedSecondStateRow state := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAudited_secondRow_eq_of_decode row state hdecode

/--
[sixVertexFourByFourAudited_firstDecode_state](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourParameterCompleteness.lean)
-/
@[path]
private lemma sixVertexFourByFourAudited_firstDecode_state_eq
  {state : Fin 4} :
-- imply
  sixVertexFourByFourAuditedFirstStateDecode (sixVertexFourByFourAuditedFirstStateRow state) = some state := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAudited_firstDecode_state state

/--
[sixVertexFourByFourAudited_secondDecode_state](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourParameterCompleteness.lean)
-/
@[path]
private lemma sixVertexFourByFourAudited_secondDecode_state_eq
  {state : Fin 4} :
-- imply
  sixVertexFourByFourAuditedSecondStateDecode (sixVertexFourByFourAuditedSecondStateRow state) = some state := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAudited_secondDecode_state state

/--
[sixVertexFourByFourAudited_nextVerticalRow_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourParameterCompleteness.lean)
-/
@[path]
private lemma sixVertexFourByFourAudited_nextVerticalRow_zero_eq
  {below : SixVertexRow 4} :
-- imply
  sixVertexFourByFourNextVerticalRow (sixVertexFourByFourRowOfMask 0) below = below := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAudited_nextVerticalRow_zero below

/--
[sixVertexFourByFourAudited_nextVerticalRow_fifteen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourParameterCompleteness.lean)
-/
@[path]
private lemma sixVertexFourByFourAudited_nextVerticalRow_fifteen_eq
  {below : SixVertexRow 4} :
-- imply
  sixVertexFourByFourNextVerticalRow (sixVertexFourByFourRowOfMask 15) below = below := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAudited_nextVerticalRow_fifteen below

/--
[sixVertexFourByFourAudited_firstVerticalRow_three_eq_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourParameterCompleteness.lean)
-/
@[path]
private lemma sixVertexFourByFourAudited_firstVerticalRow_three_eq_two_eq
  {p : SixVertexFourByFourAuditedHorizontalParameters}
  {seam : Fin 4} :
-- imply
  sixVertexFourByFourAuditedParamVerticalRowsFirst p seam 3 = sixVertexFourByFourAuditedParamVerticalRowsFirst p seam 2 := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAudited_firstVerticalRow_three_eq_two p seam

/--
[sixVertexFourByFourAudited_secondVerticalRow_three_eq_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourParameterCompleteness.lean)
-/
@[path]
private lemma sixVertexFourByFourAudited_secondVerticalRow_three_eq_two_eq
  {p : SixVertexFourByFourAuditedHorizontalParameters}
  {seam : Fin 4} :
-- imply
  sixVertexFourByFourAuditedParamVerticalRowsSecond p seam 3 = sixVertexFourByFourAuditedParamVerticalRowsSecond p seam 2 := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAudited_secondVerticalRow_three_eq_two p seam

/--
[sixVertexFourByFourAudited_firstMiddlePath_of_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourParameterCompleteness.lean)
-/
@[path]
private lemma sixVertexFourByFourAudited_firstMiddlePath_of_valid_eq
  {p : SixVertexFourByFourAuditedHorizontalParameters}
  {firstSeam secondSeam : Fin 4}
-- given
  (hrowZero : sixVertexFourByFourAuditedCoordinateRowZero firstSeam secondSeam = p.1)
  (hice : (sixVertexFourByFourAuditedParamSourceFirst p firstSeam).IceRule)
  (hsector : sixVertexUpCount (svTorusVerticalRows sixVertexFourByFourTorus (sixVertexFourByFourAuditedParamSourceFirst p firstSeam) (svFinLast sixVertexFourByFourTorus.height_pos)) = 1) :
-- imply
  (sixVertexFourByFourAuditedFirstTransition (sixVertexFourByFourAuditedOppositeSeam firstSeam) p.2.1 >>= fun s => sixVertexFourByFourAuditedFirstTransition s p.2.2.1) = some firstSeam := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAudited_firstMiddlePath_of_valid p firstSeam secondSeam hrowZero hice hsector

/--
[sixVertexFourByFourAudited_secondMiddlePath_of_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourParameterCompleteness.lean)
-/
@[path]
private lemma sixVertexFourByFourAudited_secondMiddlePath_of_valid_eq
  {p : SixVertexFourByFourAuditedHorizontalParameters}
  {firstSeam secondSeam : Fin 4}
-- given
  (hrowZero : sixVertexFourByFourAuditedCoordinateRowZero firstSeam secondSeam = p.1)
  (hice : (sixVertexFourByFourAuditedParamSourceSecond p secondSeam).IceRule)
  (hsector : sixVertexUpCount (svTorusVerticalRows sixVertexFourByFourTorus (sixVertexFourByFourAuditedParamSourceSecond p secondSeam) (svFinLast sixVertexFourByFourTorus.height_pos)) = 3) :
-- imply
  (sixVertexFourByFourAuditedSecondTransition (sixVertexFourByFourAuditedOppositeSeam secondSeam) p.2.1 >>= fun s => sixVertexFourByFourAuditedSecondTransition s p.2.2.1) = some secondSeam := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAudited_secondMiddlePath_of_valid p firstSeam secondSeam hrowZero hice hsector

/--
[sixVertexFourByFourAudited_parameterValid_uniqueCoordinate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourParameterCompleteness.lean)
-/
@[path]
private lemma sixVertexFourByFourAudited_parameterValid_uniqueCoordinate_eq
  {p : SixVertexFourByFourAuditedHorizontalParameters}
-- given
  (hvalid : SixVertexFourByFourAuditedParameterValid p) :
-- imply
  ∃! c : SixVertexFourByFourAuditedCoordinates, sixVertexFourByFourAuditedCoordinateParameters c = p := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAudited_parameterValid_uniqueCoordinate p hvalid

/--
[sixVertexFourByFourAudited_decodedSeams_coordinateRowZero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourParameterCompleteness.lean)
-/
@[path]
private lemma sixVertexFourByFourAudited_decodedSeams_coordinateRowZero_eq
  {firstSeam secondSeam : Fin 4} :
-- imply
  sixVertexFourByFourAuditedDecodedSeams (sixVertexFourByFourAuditedCoordinateRowZero firstSeam secondSeam) = (firstSeam, secondSeam) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAudited_decodedSeams_coordinateRowZero firstSeam secondSeam

/--
[sixVertexFourByFourAudited_coordinateParameters_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourParameterCompleteness.lean)
-/
@[path]
private lemma sixVertexFourByFourAudited_coordinateParameters_valid_eq
  {c : SixVertexFourByFourAuditedCoordinates} :
-- imply
  SixVertexFourByFourAuditedParameterValid (sixVertexFourByFourAuditedCoordinateParameters c) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAudited_coordinateParameters_valid c

/--
[sixVertexFourByFourAudited_validParameterSet_eq_coordinateImage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourParameterCompleteness.lean)
-/
@[path]
private lemma sixVertexFourByFourAudited_validParameterSet_eq_coordinateImage_eq :
-- imply
  sixVertexFourByFourAuditedValidParameterSet = sixVertexFourByFourAuditedCoordinateParameterImage := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAudited_validParameterSet_eq_coordinateImage

/--
[sixVertexFourByFourAudited_validParameterSet_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourParameterCompleteness.lean)
-/
@[path]
private lemma sixVertexFourByFourAudited_validParameterSet_card_eq :
-- imply
  sixVertexFourByFourAuditedValidParameterSet.card = 512 := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAudited_validParameterSet_card

/--
[sixVertexFourByFourAuditedValidParameterCoordinate_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourParameterCompleteness.lean)
-/
@[path]
private lemma sixVertexFourByFourAuditedValidParameterCoordinate_spec_eq
  {p : SixVertexFourByFourAuditedValidParameter} :
-- imply
  sixVertexFourByFourAuditedCoordinateParameters (sixVertexFourByFourAuditedValidParameterCoordinate p) = p.1 := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAuditedValidParameterCoordinate_spec p

/--
[sixVertexFourByFourAuditedValidParameterCoordinate_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourParameterCompleteness.lean)
-/
@[path]
private lemma sixVertexFourByFourAuditedValidParameterCoordinate_injective_eq :
-- imply
  Function.Injective sixVertexFourByFourAuditedValidParameterCoordinate := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAuditedValidParameterCoordinate_injective

/--
[sixVertexFourByFourAuditedValidParameter_source_eq_coordinateSource](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourParameterCompleteness.lean)
-/
@[path]
private lemma sixVertexFourByFourAuditedValidParameter_source_eq_coordinateSource_eq
  {p : SixVertexFourByFourAuditedValidParameter} :
-- imply
  sixVertexFourByFourAuditedValidParameterSourcePair p = sixVertexFourByFourAuditedCoordinateSourcePair (sixVertexFourByFourAuditedValidParameterCoordinate p) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAuditedValidParameter_source_eq_coordinateSource p

/--
[sixVertexFourByFourAuditedValidParameter_matching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourParameterCompleteness.lean)
-/
@[path]
private lemma sixVertexFourByFourAuditedValidParameter_matching_eq :
-- imply
  Function.Injective sixVertexFourByFourAuditedValidParameterSourcePair /\ Function.Injective sixVertexFourByFourAuditedValidParameterTargetPair /\ forall p, SixVertexFourByFourAuditedParameterValid p.1 /\ SixVertexFourByFourAuditedCoordinateTargetPairValid (sixVertexFourByFourAuditedValidParameterCoordinate p) /\ sixVertexPairAtMostTwoCycleFineRelated (sixVertexFourByFourAuditedValidParameterSourcePair p) (sixVertexFourByFourAuditedValidParameterTargetPair p) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAuditedValidParameter_matching


-- created on 2026-10-23
