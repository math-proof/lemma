import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourRowAutomaton.Part4
open StatMech StatMech.FrontierD


/--
[sixVertexFourByFourAudited_nextVerticalRow_eq_of_ice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourRowAutomaton.lean)
-/
@[path]
private lemma sixVertexFourByFourAudited_nextVerticalRow_eq_of_ice_eq
-- given
  (below current horizontal : SixVertexRow 4)
  (hice : svHorizontalIce (by norm_num) below current horizontal) :
-- imply
  sixVertexFourByFourNextVerticalRow horizontal below = current := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAudited_nextVerticalRow_eq_of_ice below current horizontal hice

/--
[sixVertexFourByFourAudited_firstStateCode_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourRowAutomaton.lean)
-/
@[path]
private lemma sixVertexFourByFourAudited_firstStateCode_iff_eq
  {row : SixVertexRow 4} :
-- imply
  sixVertexUpCount row = 1 <-> Nat.ofBits row = 1 \/ Nat.ofBits row = 2 \/ Nat.ofBits row = 4 \/ Nat.ofBits row = 8 := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAudited_firstStateCode_iff row

/--
[sixVertexFourByFourAudited_secondStateCode_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourRowAutomaton.lean)
-/
@[path]
private lemma sixVertexFourByFourAudited_secondStateCode_iff_eq
  {row : SixVertexRow 4} :
-- imply
  sixVertexUpCount row = 3 <-> Nat.ofBits row = 7 \/ Nat.ofBits row = 11 \/ Nat.ofBits row = 13 \/ Nat.ofBits row = 14 := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAudited_secondStateCode_iff row

/--
[sixVertexFourByFourAudited_firstStateDecode_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourRowAutomaton.lean)
-/
@[path]
private lemma sixVertexFourByFourAudited_firstStateDecode_spec_eq
  {row : SixVertexRow 4} :
-- imply
  match sixVertexFourByFourAuditedFirstStateDecode row with := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAudited_firstStateDecode_spec row

/--
[sixVertexFourByFourAudited_secondStateDecode_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourRowAutomaton.lean)
-/
@[path]
private lemma sixVertexFourByFourAudited_secondStateDecode_spec_eq
  {row : SixVertexRow 4} :
-- imply
  match sixVertexFourByFourAuditedSecondStateDecode row with := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAudited_secondStateDecode_spec row

/--
[sixVertexFourByFourAudited_firstTransition_table](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourRowAutomaton.lean)
-/
@[path]
private lemma sixVertexFourByFourAudited_firstTransition_table_eq
  {state : Fin 4}
  {middle : Fin 16} :
-- imply
  sixVertexFourByFourAuditedFirstTransition state middle = sixVertexFourByFourAuditedFirstTransitionTable state middle := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAudited_firstTransition_table state middle

/--
[sixVertexFourByFourAudited_secondTransition_table](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourRowAutomaton.lean)
-/
@[path]
private lemma sixVertexFourByFourAudited_secondTransition_table_eq
  {state : Fin 4}
  {middle : Fin 16} :
-- imply
  sixVertexFourByFourAuditedSecondTransition state middle = sixVertexFourByFourAuditedSecondTransitionTable state middle := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAudited_secondTransition_table state middle

/--
[sixVertexFourByFourAudited_firstRowZero_opposite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourRowAutomaton.lean)
-/
@[path]
private lemma sixVertexFourByFourAudited_firstRowZero_opposite_eq
  {firstSeam secondSeam : Fin 4} :
-- imply
  sixVertexFourByFourAuditedFirstStateDecode (sixVertexFourByFourNextVerticalRow (sixVertexFourByFourRowOfMask (sixVertexFourByFourAuditedRowZero (sixVertexFourByFourAuditedCoordinateRowZero firstSeam secondSeam)).1) (sixVertexFourByFourAuditedFirstStateRow firstSeam)) = some (sixVertexFourByFourAuditedOppositeSeam firstSeam) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAudited_firstRowZero_opposite firstSeam secondSeam

/--
[sixVertexFourByFourAudited_secondRowZero_opposite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourRowAutomaton.lean)
-/
@[path]
private lemma sixVertexFourByFourAudited_secondRowZero_opposite_eq
  {firstSeam secondSeam : Fin 4} :
-- imply
  sixVertexFourByFourAuditedSecondStateDecode (sixVertexFourByFourNextVerticalRow (sixVertexFourByFourRowOfMask (sixVertexFourByFourAuditedRowZero (sixVertexFourByFourAuditedCoordinateRowZero firstSeam secondSeam)).2) (sixVertexFourByFourAuditedSecondStateRow secondSeam)) = some (sixVertexFourByFourAuditedOppositeSeam secondSeam) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAudited_secondRowZero_opposite firstSeam secondSeam

/--
[sixVertexFourByFourAudited_firstPath_iff_cross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourRowAutomaton.lean)
-/
@[path]
private lemma sixVertexFourByFourAudited_firstPath_iff_cross_eq
  {seam : Fin 4}
  {firstMiddle secondMiddle : Fin 16} :
-- imply
  (sixVertexFourByFourAuditedFirstTransition (sixVertexFourByFourAuditedOppositeSeam seam) firstMiddle >>= fun s => sixVertexFourByFourAuditedFirstTransition s secondMiddle) = some seam <-> sixVertexFourByFourAuditedFirstCrossB seam firstMiddle secondMiddle = true := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAudited_firstPath_iff_cross seam firstMiddle secondMiddle

/--
[sixVertexFourByFourAudited_secondPath_iff_cross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourRowAutomaton.lean)
-/
@[path]
private lemma sixVertexFourByFourAudited_secondPath_iff_cross_eq
  {seam : Fin 4}
  {firstMiddle secondMiddle : Fin 16} :
-- imply
  (sixVertexFourByFourAuditedSecondTransition (sixVertexFourByFourAuditedOppositeSeam seam) firstMiddle >>= fun s => sixVertexFourByFourAuditedSecondTransition s secondMiddle) = some seam <-> sixVertexFourByFourAuditedSecondCrossB seam firstMiddle secondMiddle = true := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAudited_secondPath_iff_cross seam firstMiddle secondMiddle

/--
[sixVertexFourByFourAudited_crosses_iff_template](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourRowAutomaton.lean)
-/
@[path]
private lemma sixVertexFourByFourAudited_crosses_iff_template_eq
  {firstSeam secondSeam : Fin 4}
  {firstMiddle secondMiddle : Fin 16} :
-- imply
  sixVertexFourByFourAuditedFirstCrossB firstSeam firstMiddle secondMiddle = true /\ sixVertexFourByFourAuditedSecondCrossB secondSeam firstMiddle secondMiddle = true <-> exists middle : Fin 8, (firstMiddle, secondMiddle) = sixVertexFourByFourAuditedMiddlePair firstSeam secondSeam middle := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAudited_crosses_iff_template firstSeam secondSeam firstMiddle secondMiddle

/--
[sixVertexFourByFourAudited_middlePathAllowed_iff_template](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourRowAutomaton.lean)
-/
@[path]
private lemma sixVertexFourByFourAudited_middlePathAllowed_iff_template_eq
  {firstSeam secondSeam : Fin 4}
  {firstMiddle secondMiddle : Fin 16} :
-- imply
  sixVertexFourByFourAuditedMiddlePathAllowed firstSeam secondSeam firstMiddle secondMiddle <-> exists middle : Fin 8, (firstMiddle, secondMiddle) = sixVertexFourByFourAuditedMiddlePair firstSeam secondSeam middle := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAudited_middlePathAllowed_iff_template firstSeam secondSeam firstMiddle secondMiddle


-- created on 2026-10-23
