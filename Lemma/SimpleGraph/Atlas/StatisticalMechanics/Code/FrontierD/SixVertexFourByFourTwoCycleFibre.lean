import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourTwoCycleFibre.Part13
open StatMech StatMech.FrontierD


/--
[sixVertexFourByFourOppositeVerticalColumnFamily_horizontalFlow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleFibre.lean)
-/
@[path]
private lemma sixVertexFourByFourOppositeVerticalColumnFamily_horizontalFlow_eq
  {firstColumn secondColumn : Fin 4}
  {v : sixVertexFourByFourTorus.Vertex}
-- given
  (hne : firstColumn ≠ secondColumn) :
-- imply
  (sixVertexFourByFourOppositeVerticalColumnFamily firstColumn secondColumn hne).horizontalFlow v = 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourOppositeVerticalColumnFamily_horizontalFlow firstColumn secondColumn hne v

/--
[sixVertexFourByFourOppositeVerticalColumnFamily_verticalFlow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleFibre.lean)
-/
@[path]
private lemma sixVertexFourByFourOppositeVerticalColumnFamily_verticalFlow_eq
  {firstColumn secondColumn : Fin 4}
  {x y : Fin 4}
-- given
  (hne : firstColumn ≠ secondColumn) :
-- imply
  (sixVertexFourByFourOppositeVerticalColumnFamily firstColumn secondColumn hne).verticalFlow (x, y) = (if x = firstColumn then 1 else if x = secondColumn then -1 else 0) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourOppositeVerticalColumnFamily_verticalFlow firstColumn secondColumn hne x y

/--
[sixVertexFourByFourAudited_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleFibre.lean)
-/
@[path]
private lemma sixVertexFourByFourAudited_valid_eq :
-- imply
  sixVertexFourByFourAuditedSourceFirst.IceRule /\ sixVertexFourByFourAuditedSourceSecond.IceRule /\ sixVertexFourByFourAuditedTargetFirst.IceRule /\ sixVertexFourByFourAuditedTargetSecond.IceRule /\ sixVertexUpCount (svTorusVerticalRows sixVertexFourByFourTorus sixVertexFourByFourAuditedSourceFirst (svFinLast sixVertexFourByFourTorus.height_pos)) = 1 /\ sixVertexUpCount (svTorusVerticalRows sixVertexFourByFourTorus sixVertexFourByFourAuditedSourceSecond (svFinLast sixVertexFourByFourTorus.height_pos)) = 3 /\ sixVertexUpCount (svTorusVerticalRows sixVertexFourByFourTorus sixVertexFourByFourAuditedTargetFirst (svFinLast sixVertexFourByFourTorus.height_pos)) = 2 /\ sixVertexUpCount (svTorusVerticalRows sixVertexFourByFourTorus sixVertexFourByFourAuditedTargetSecond (svFinLast sixVertexFourByFourTorus.height_pos)) = 2 := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAudited_valid

/--
[sixVertexFourByFourAudited_twoCycleRelated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleFibre.lean)
-/
@[path]
private lemma sixVertexFourByFourAudited_twoCycleRelated_eq :
-- imply
  sixVertexPairAtMostTwoCycleRelated (sixVertexFourByFourAuditedSourceFirst, sixVertexFourByFourAuditedSourceSecond) (sixVertexFourByFourAuditedTargetFirst, sixVertexFourByFourAuditedTargetSecond) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAudited_twoCycleRelated

/--
[sixVertexFourByFourAudited_fineRelated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleFibre.lean)
-/
@[path]
private lemma sixVertexFourByFourAudited_fineRelated_eq :
-- imply
  sixVertexPairAtMostTwoCycleFineRelated (sixVertexFourByFourAuditedSourceFirst, sixVertexFourByFourAuditedSourceSecond) (sixVertexFourByFourAuditedTargetFirst, sixVertexFourByFourAuditedTargetSecond) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAudited_fineRelated

/--
[sixVertexFourByFourMaskOfRowMasks_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleFibre.lean)
-/
@[path]
private lemma sixVertexFourByFourMaskOfRowMasks_apply_eq
  {x y : Fin 4}
-- given
  (rows : Fin 4 -> Nat) :
-- imply
  (sixVertexFourByFourMaskOfRowMasks rows).testBit (y.val * 4 + x.val) = (rows y).testBit x.val := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourMaskOfRowMasks_apply rows x y

/--
[sixVertexFourByFourMaskOfRowMasks_testBit_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleFibre.lean)
-/
@[path]
private lemma sixVertexFourByFourMaskOfRowMasks_testBit_zero_eq
  {x : Fin 4}
-- given
  (rows : Fin 4 -> Nat) :
-- imply
  (sixVertexFourByFourMaskOfRowMasks rows).testBit x.val = (rows 0).testBit x.val := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourMaskOfRowMasks_testBit_zero rows x

/--
[sixVertexFourByFourMaskOfRowMasks_testBit_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleFibre.lean)
-/
@[path]
private lemma sixVertexFourByFourMaskOfRowMasks_testBit_one_eq
  {x : Fin 4}
-- given
  (rows : Fin 4 -> Nat) :
-- imply
  (sixVertexFourByFourMaskOfRowMasks rows).testBit (4 + x.val) = (rows 1).testBit x.val := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourMaskOfRowMasks_testBit_one rows x

/--
[sixVertexFourByFourMaskOfRowMasks_testBit_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleFibre.lean)
-/
@[path]
private lemma sixVertexFourByFourMaskOfRowMasks_testBit_two_eq
  {x : Fin 4}
-- given
  (rows : Fin 4 -> Nat) :
-- imply
  (sixVertexFourByFourMaskOfRowMasks rows).testBit (8 + x.val) = (rows 2).testBit x.val := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourMaskOfRowMasks_testBit_two rows x

/--
[sixVertexFourByFourMaskOfRowMasks_testBit_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleFibre.lean)
-/
@[path]
private lemma sixVertexFourByFourMaskOfRowMasks_testBit_three_eq
  {x : Fin 4}
-- given
  (rows : Fin 4 -> Nat) :
-- imply
  (sixVertexFourByFourMaskOfRowMasks rows).testBit (12 + x.val) = (rows 3).testBit x.val := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourMaskOfRowMasks_testBit_three rows x

/--
[sixVertexFourByFourEvenUpCount_preserved](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleFibre.lean)
-/
@[path]
private lemma sixVertexFourByFourEvenUpCount_preserved_eq
  {i : Fin 6}
  {previous current : SixVertexRow 4}
-- given
  (hice : svHorizontalIce (by norm_num) previous current (sixVertexFourByFourRowOfMask (sixVertexFourByFourAllowedHorizontalMask i))) :
-- imply
  sixVertexFourByFourEvenUpCount previous = sixVertexFourByFourEvenUpCount current := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourEvenUpCount_preserved i previous current hice

/--
[sixVertexFourByFourNextVerticalRow_ice_of_upCount_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleFibre.lean)
-/
@[path]
private lemma sixVertexFourByFourNextVerticalRow_ice_of_upCount_eq_eq
  {i : Fin 6}
  {below : SixVertexRow 4}
-- given
  (hcount : sixVertexUpCount (sixVertexFourByFourNextVerticalRow (sixVertexFourByFourRowOfMask (sixVertexFourByFourAllowedHorizontalMask i)) below) = sixVertexUpCount below) :
-- imply
  svHorizontalIce (by norm_num) below (sixVertexFourByFourNextVerticalRow (sixVertexFourByFourRowOfMask (sixVertexFourByFourAllowedHorizontalMask i)) below) (sixVertexFourByFourRowOfMask (sixVertexFourByFourAllowedHorizontalMask i)) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourNextVerticalRow_ice_of_upCount_eq i below hcount

/--
[sixVertexFourByFourFirstRowZero_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleFibre.lean)
-/
@[path]
private lemma sixVertexFourByFourFirstRowZero_even_eq
  {p0 : Fin 16}
  {seam : Fin 4}
-- given
  (hcount : sixVertexUpCount (sixVertexFourByFourNextVerticalRow (sixVertexFourByFourRowOfMask (sixVertexFourByFourAuditedRowZero p0).1) (sixVertexFourByFourRowOfMask (sixVertexFourByFourSectorOneSeamMask seam))) = 1) :
-- imply
  sixVertexFourByFourEvenUpCount (sixVertexFourByFourNextVerticalRow (sixVertexFourByFourRowOfMask (sixVertexFourByFourAuditedRowZero p0).1) (sixVertexFourByFourRowOfMask (sixVertexFourByFourSectorOneSeamMask seam))) = sixVertexFourByFourEvenUpCount (sixVertexFourByFourRowOfMask (sixVertexFourByFourSectorOneSeamMask seam)) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourFirstRowZero_even p0 seam hcount

/--
[sixVertexFourByFourSecondRowZero_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleFibre.lean)
-/
@[path]
private lemma sixVertexFourByFourSecondRowZero_even_eq
  {p0 : Fin 16}
  {seam : Fin 4}
-- given
  (hcount : sixVertexUpCount (sixVertexFourByFourNextVerticalRow (sixVertexFourByFourRowOfMask (sixVertexFourByFourAuditedRowZero p0).2) (sixVertexFourByFourRowOfMask (sixVertexFourByFourSectorThreeSeamMask seam))) = 3) :
-- imply
  sixVertexFourByFourEvenUpCount (sixVertexFourByFourNextVerticalRow (sixVertexFourByFourRowOfMask (sixVertexFourByFourAuditedRowZero p0).2) (sixVertexFourByFourRowOfMask (sixVertexFourByFourSectorThreeSeamMask seam))) = sixVertexFourByFourEvenUpCount (sixVertexFourByFourRowOfMask (sixVertexFourByFourSectorThreeSeamMask seam)) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourSecondRowZero_even p0 seam hcount

/--
[sixVertexFourByFourAllowedHorizontalIndex_rowZero_first](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleFibre.lean)
-/
@[path]
private lemma sixVertexFourByFourAllowedHorizontalIndex_rowZero_first_eq
  {p : Fin 16} :
-- imply
  sixVertexFourByFourAllowedHorizontalMask (sixVertexFourByFourAllowedHorizontalIndex (sixVertexFourByFourAuditedRowZero p).1) = (sixVertexFourByFourAuditedRowZero p).1 := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAllowedHorizontalIndex_rowZero_first p

/--
[sixVertexFourByFourAllowedHorizontalIndex_rowZero_second](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleFibre.lean)
-/
@[path]
private lemma sixVertexFourByFourAllowedHorizontalIndex_rowZero_second_eq
  {p : Fin 16} :
-- imply
  sixVertexFourByFourAllowedHorizontalMask (sixVertexFourByFourAllowedHorizontalIndex (sixVertexFourByFourAuditedRowZero p).2) = (sixVertexFourByFourAuditedRowZero p).2 := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAllowedHorizontalIndex_rowZero_second p

/--
[sixVertexFourByFourAllowedHorizontalIndex_rowMiddle_first](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleFibre.lean)
-/
@[path]
private lemma sixVertexFourByFourAllowedHorizontalIndex_rowMiddle_first_eq
  {p : Fin 16} :
-- imply
  sixVertexFourByFourAllowedHorizontalMask (sixVertexFourByFourAllowedHorizontalIndex (sixVertexFourByFourAuditedRowMiddle p).1) = (sixVertexFourByFourAuditedRowMiddle p).1 := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAllowedHorizontalIndex_rowMiddle_first p

/--
[sixVertexFourByFourAllowedHorizontalIndex_rowMiddle_second](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleFibre.lean)
-/
@[path]
private lemma sixVertexFourByFourAllowedHorizontalIndex_rowMiddle_second_eq
  {p : Fin 16} :
-- imply
  sixVertexFourByFourAllowedHorizontalMask (sixVertexFourByFourAllowedHorizontalIndex (sixVertexFourByFourAuditedRowMiddle p).2) = (sixVertexFourByFourAuditedRowMiddle p).2 := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAllowedHorizontalIndex_rowMiddle_second p

/--
[sixVertexFourByFourAllowedHorizontalIndex_rowLast_first](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleFibre.lean)
-/
@[path]
private lemma sixVertexFourByFourAllowedHorizontalIndex_rowLast_first_eq
  {p : Fin 4} :
-- imply
  sixVertexFourByFourAllowedHorizontalMask (sixVertexFourByFourAllowedHorizontalIndex (sixVertexFourByFourAuditedRowLast p).1) = (sixVertexFourByFourAuditedRowLast p).1 := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAllowedHorizontalIndex_rowLast_first p

/--
[sixVertexFourByFourAllowedHorizontalIndex_rowLast_second](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleFibre.lean)
-/
@[path]
private lemma sixVertexFourByFourAllowedHorizontalIndex_rowLast_second_eq
  {p : Fin 4} :
-- imply
  sixVertexFourByFourAllowedHorizontalMask (sixVertexFourByFourAllowedHorizontalIndex (sixVertexFourByFourAuditedRowLast p).2) = (sixVertexFourByFourAuditedRowLast p).2 := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAllowedHorizontalIndex_rowLast_second p

/--
[sixVertexFourByFourAuditedParamHorizontalRowsFirst_allowed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleFibre.lean)
-/
@[path]
private lemma sixVertexFourByFourAuditedParamHorizontalRowsFirst_allowed_eq
  {p : SixVertexFourByFourAuditedHorizontalParameters}
  {y : Fin 4} :
-- imply
  ∃ i, sixVertexFourByFourAuditedParamHorizontalRowsFirst p y = sixVertexFourByFourRowOfMask (sixVertexFourByFourAllowedHorizontalMask i) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAuditedParamHorizontalRowsFirst_allowed p y

/--
[sixVertexFourByFourAuditedParamHorizontalRowsSecond_allowed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleFibre.lean)
-/
@[path]
private lemma sixVertexFourByFourAuditedParamHorizontalRowsSecond_allowed_eq
  {p : SixVertexFourByFourAuditedHorizontalParameters}
  {y : Fin 4} :
-- imply
  ∃ i, sixVertexFourByFourAuditedParamHorizontalRowsSecond p y = sixVertexFourByFourRowOfMask (sixVertexFourByFourAllowedHorizontalMask i) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAuditedParamHorizontalRowsSecond_allowed p y

/--
[sixVertexFourByFourVerticalMaskOfRows_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleFibre.lean)
-/
@[path]
private lemma sixVertexFourByFourVerticalMaskOfRows_apply_eq
  {x y : Fin 4}
-- given
  (rows : Fin 4 -> SixVertexRow 4) :
-- imply
  (sixVertexFourByFourVerticalMaskOfRows rows).testBit (y.val * 4 + x.val) = rows y x := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourVerticalMaskOfRows_apply rows x y

/--
[sixVertexFourByFourCompletedVerticalMask_row](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleFibre.lean)
-/
@[path]
private lemma sixVertexFourByFourCompletedVerticalMask_row_eq
  {x y : Fin 4}
-- given
  (horizontalMask seamMask : Nat) :
-- imply
  (sixVertexFourByFourArrowsOfMasks horizontalMask (sixVertexFourByFourCompletedVerticalMask horizontalMask seamMask)).vertical (x, y) = sixVertexFourByFourCompletedVerticalRow horizontalMask seamMask y x := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourCompletedVerticalMask_row horizontalMask seamMask x y

/--
[sixVertexFourByFourCompletedVerticalColumn_auditedFirst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleFibre.lean)
-/
@[path]
private lemma sixVertexFourByFourCompletedVerticalColumn_auditedFirst_eq
  {p : SixVertexFourByFourAuditedHorizontalParameters}
  {seam x y : Fin 4} :
-- imply
  sixVertexFourByFourCompletedVerticalColumn (sixVertexFourByFourAuditedHorizontalMasks p).1 (sixVertexFourByFourSectorOneSeamMask seam) x y = sixVertexFourByFourAuditedParamVerticalRowsFirst p seam y x := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourCompletedVerticalColumn_auditedFirst p seam x y

/--
[sixVertexFourByFourCompletedVerticalColumn_auditedSecond](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleFibre.lean)
-/
@[path]
private lemma sixVertexFourByFourCompletedVerticalColumn_auditedSecond_eq
  {p : SixVertexFourByFourAuditedHorizontalParameters}
  {seam x y : Fin 4} :
-- imply
  sixVertexFourByFourCompletedVerticalColumn (sixVertexFourByFourAuditedHorizontalMasks p).2 (sixVertexFourByFourSectorThreeSeamMask seam) x y = sixVertexFourByFourAuditedParamVerticalRowsSecond p seam y x := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourCompletedVerticalColumn_auditedSecond p seam x y

/--
[sixVertexFourByFour_rowIce](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleFibre.lean)
-/
@[path]
private lemma sixVertexFourByFour_rowIce_eq
  {omega : SixVertexArrows sixVertexFourByFourTorus}
  {y : Fin 4}
-- given
  (hice : omega.IceRule) :
-- imply
  svHorizontalIce sixVertexFourByFourTorus.width_pos (svTorusVerticalRows sixVertexFourByFourTorus omega (SixVertexArrows.cyclicPred sixVertexFourByFourTorus.height_pos y)) (svTorusVerticalRows sixVertexFourByFourTorus omega y) (svTorusHorizontalRows sixVertexFourByFourTorus omega y) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFour_rowIce omega hice y

/--
[sixVertexFourByFour_verticalRowCount_eq_last](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleFibre.lean)
-/
@[path]
private lemma sixVertexFourByFour_verticalRowCount_eq_last_eq
  {omega : SixVertexArrows sixVertexFourByFourTorus}
  {y : Fin 4}
-- given
  (hice : omega.IceRule) :
-- imply
  sixVertexUpCount (svTorusVerticalRows sixVertexFourByFourTorus omega y) = sixVertexUpCount (svTorusVerticalRows sixVertexFourByFourTorus omega (svFinLast sixVertexFourByFourTorus.height_pos)) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFour_verticalRowCount_eq_last omega hice y

/--
[sixVertexFourByFourAuditedParamSourceFirst_eq_completedMasks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleFibre.lean)
-/
@[path]
private lemma sixVertexFourByFourAuditedParamSourceFirst_eq_completedMasks_eq
  {p : SixVertexFourByFourAuditedHorizontalParameters}
  {seam : Fin 4} :
-- imply
  sixVertexFourByFourAuditedParamSourceFirst p seam = sixVertexFourByFourArrowsOfMasks (sixVertexFourByFourAuditedHorizontalMasks p).1 (sixVertexFourByFourCompletedVerticalMask (sixVertexFourByFourAuditedHorizontalMasks p).1 (sixVertexFourByFourSectorOneSeamMask seam)) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAuditedParamSourceFirst_eq_completedMasks p seam

/--
[sixVertexFourByFourAuditedParamSourceSecond_eq_completedMasks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleFibre.lean)
-/
@[path]
private lemma sixVertexFourByFourAuditedParamSourceSecond_eq_completedMasks_eq
  {p : SixVertexFourByFourAuditedHorizontalParameters}
  {seam : Fin 4} :
-- imply
  sixVertexFourByFourAuditedParamSourceSecond p seam = sixVertexFourByFourArrowsOfMasks (sixVertexFourByFourAuditedHorizontalMasks p).2 (sixVertexFourByFourCompletedVerticalMask (sixVertexFourByFourAuditedHorizontalMasks p).2 (sixVertexFourByFourSectorThreeSeamMask seam)) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAuditedParamSourceSecond_eq_completedMasks p seam

/--
[sixVertexFourByFourAuditedParamSourceFirst_verticalRowCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleFibre.lean)
-/
@[path]
private lemma sixVertexFourByFourAuditedParamSourceFirst_verticalRowCount_eq
  {p : SixVertexFourByFourAuditedHorizontalParameters}
  {seam y : Fin 4}
-- given
  (hice : (sixVertexFourByFourAuditedParamSourceFirst p seam).IceRule)
  (hsector : sixVertexUpCount (svTorusVerticalRows sixVertexFourByFourTorus (sixVertexFourByFourAuditedParamSourceFirst p seam) (svFinLast sixVertexFourByFourTorus.height_pos)) = 1) :
-- imply
  sixVertexUpCount (sixVertexFourByFourAuditedParamVerticalRowsFirst p seam y) = 1 := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAuditedParamSourceFirst_verticalRowCount p seam y hice hsector

/--
[sixVertexFourByFourAuditedParamSourceSecond_verticalRowCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleFibre.lean)
-/
@[path]
private lemma sixVertexFourByFourAuditedParamSourceSecond_verticalRowCount_eq
  {p : SixVertexFourByFourAuditedHorizontalParameters}
  {seam y : Fin 4}
-- given
  (hice : (sixVertexFourByFourAuditedParamSourceSecond p seam).IceRule)
  (hsector : sixVertexUpCount (svTorusVerticalRows sixVertexFourByFourTorus (sixVertexFourByFourAuditedParamSourceSecond p seam) (svFinLast sixVertexFourByFourTorus.height_pos)) = 3) :
-- imply
  sixVertexUpCount (sixVertexFourByFourAuditedParamVerticalRowsSecond p seam y) = 3 := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAuditedParamSourceSecond_verticalRowCount p seam y hice hsector

/--
[sixVertexFourByFourAuditedParamSourceFirst_evenStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleFibre.lean)
-/
@[path]
private lemma sixVertexFourByFourAuditedParamSourceFirst_evenStep_eq
  {p : SixVertexFourByFourAuditedHorizontalParameters}
  {seam y : Fin 4}
-- given
  (hice : (sixVertexFourByFourAuditedParamSourceFirst p seam).IceRule) :
-- imply
  sixVertexFourByFourEvenUpCount (sixVertexFourByFourAuditedParamVerticalRowsFirst p seam (SixVertexArrows.cyclicPred sixVertexFourByFourTorus.height_pos y)) = sixVertexFourByFourEvenUpCount (sixVertexFourByFourAuditedParamVerticalRowsFirst p seam y) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAuditedParamSourceFirst_evenStep p seam y hice

/--
[sixVertexFourByFourAuditedParamSourceSecond_evenStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleFibre.lean)
-/
@[path]
private lemma sixVertexFourByFourAuditedParamSourceSecond_evenStep_eq
  {p : SixVertexFourByFourAuditedHorizontalParameters}
  {seam y : Fin 4}
-- given
  (hice : (sixVertexFourByFourAuditedParamSourceSecond p seam).IceRule) :
-- imply
  sixVertexFourByFourEvenUpCount (sixVertexFourByFourAuditedParamVerticalRowsSecond p seam (SixVertexArrows.cyclicPred sixVertexFourByFourTorus.height_pos y)) = sixVertexFourByFourEvenUpCount (sixVertexFourByFourAuditedParamVerticalRowsSecond p seam y) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAuditedParamSourceSecond_evenStep p seam y hice

/--
[sixVertexFourByFourAuditedParamSourceFirst_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleFibre.lean)
-/
@[path]
private lemma sixVertexFourByFourAuditedParamSourceFirst_even_eq
  {p : SixVertexFourByFourAuditedHorizontalParameters}
  {seam y : Fin 4}
-- given
  (hice : (sixVertexFourByFourAuditedParamSourceFirst p seam).IceRule)
  (hsector : sixVertexUpCount (svTorusVerticalRows sixVertexFourByFourTorus (sixVertexFourByFourAuditedParamSourceFirst p seam) (svFinLast sixVertexFourByFourTorus.height_pos)) = 1) :
-- imply
  sixVertexFourByFourEvenUpCount (sixVertexFourByFourAuditedParamVerticalRowsFirst p seam y) = sixVertexFourByFourEvenUpCount (sixVertexFourByFourRowOfMask (sixVertexFourByFourSectorOneSeamMask seam)) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAuditedParamSourceFirst_even p seam y hice hsector

/--
[sixVertexFourByFourAuditedParamSourceSecond_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleFibre.lean)
-/
@[path]
private lemma sixVertexFourByFourAuditedParamSourceSecond_even_eq
  {p : SixVertexFourByFourAuditedHorizontalParameters}
  {seam y : Fin 4}
-- given
  (hice : (sixVertexFourByFourAuditedParamSourceSecond p seam).IceRule)
  (hsector : sixVertexUpCount (svTorusVerticalRows sixVertexFourByFourTorus (sixVertexFourByFourAuditedParamSourceSecond p seam) (svFinLast sixVertexFourByFourTorus.height_pos)) = 3) :
-- imply
  sixVertexFourByFourEvenUpCount (sixVertexFourByFourAuditedParamVerticalRowsSecond p seam y) = sixVertexFourByFourEvenUpCount (sixVertexFourByFourRowOfMask (sixVertexFourByFourSectorThreeSeamMask seam)) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAuditedParamSourceSecond_even p seam y hice hsector

/--
[sixVertexFourByFourSelectedFirst_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleFibre.lean)
-/
@[path]
private lemma sixVertexFourByFourSelectedFirst_false_eq
  {row : SixVertexRow 4}
  {seam : Fin 4}
-- given
  (hcount : sixVertexUpCount row = 1)
  (heven : sixVertexFourByFourEvenUpCount row = sixVertexFourByFourEvenUpCount (sixVertexFourByFourRowOfMask (sixVertexFourByFourSectorOneSeamMask seam))) :
-- imply
  row (![1, 0, 1, 0] seam) = false := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourSelectedFirst_false row seam hcount heven

/--
[sixVertexFourByFourSelectedSecond_true](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleFibre.lean)
-/
@[path]
private lemma sixVertexFourByFourSelectedSecond_true_eq
  {row : SixVertexRow 4}
  {firstSeam secondSeam : Fin 4}
-- given
  (hcount : sixVertexUpCount row = 3)
  (heven : sixVertexFourByFourEvenUpCount row = sixVertexFourByFourEvenUpCount (sixVertexFourByFourRowOfMask (sixVertexFourByFourSectorThreeSeamMask secondSeam))) :
-- imply
  row (sixVertexFourByFourAuditedRepairColumns firstSeam secondSeam).2 = true := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourSelectedSecond_true row firstSeam secondSeam hcount heven

/--
[sixVertexFourByFourToggleVerticalColumn_iceRule](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleFibre.lean)
-/
@[path]
private lemma sixVertexFourByFourToggleVerticalColumn_iceRule_eq
  {omega : SixVertexArrows sixVertexFourByFourTorus}
  {column : Fin 4}
  {value : Bool}
-- given
  (hcolumn : forall y, omega.vertical (column, y) = value)
  (hice : omega.IceRule) :
-- imply
  (sixVertexFourByFourToggleVerticalColumn column omega).IceRule := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourToggleVerticalColumn_iceRule omega column value hcolumn hice

/--
[sixVertexFourByFourToggleVerticalColumn_upCount_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleFibre.lean)
-/
@[path]
private lemma sixVertexFourByFourToggleVerticalColumn_upCount_false_eq
  {omega : SixVertexArrows sixVertexFourByFourTorus}
  {column y : Fin 4}
-- given
  (hcolumn : omega.vertical (column, y) = false) :
-- imply
  sixVertexUpCount (svTorusVerticalRows sixVertexFourByFourTorus (sixVertexFourByFourToggleVerticalColumn column omega) y) = sixVertexUpCount (svTorusVerticalRows sixVertexFourByFourTorus omega y) + 1 := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourToggleVerticalColumn_upCount_false omega column y hcolumn

/--
[sixVertexFourByFourToggleVerticalColumn_upCount_true](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleFibre.lean)
-/
@[path]
private lemma sixVertexFourByFourToggleVerticalColumn_upCount_true_eq
  {omega : SixVertexArrows sixVertexFourByFourTorus}
  {column y : Fin 4}
-- given
  (hcolumn : omega.vertical (column, y) = true) :
-- imply
  sixVertexUpCount (svTorusVerticalRows sixVertexFourByFourTorus omega y) = sixVertexUpCount (svTorusVerticalRows sixVertexFourByFourTorus (sixVertexFourByFourToggleVerticalColumn column omega) y) + 1 := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourToggleVerticalColumn_upCount_true omega column y hcolumn

/--
[sixVertexFourByFourTogglePair_fineRelated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleFibre.lean)
-/
@[path]
private lemma sixVertexFourByFourTogglePair_fineRelated_eq
  {first second : SixVertexArrows sixVertexFourByFourTorus}
  {firstColumn secondColumn : Fin 4}
-- given
  (hfirst : forall y, first.vertical (firstColumn, y) = false)
  (hsecond : forall y, second.vertical (secondColumn, y) = true) :
-- imply
  sixVertexPairAtMostTwoCycleFineRelated (first, second) (sixVertexFourByFourToggleVerticalColumn firstColumn first, sixVertexFourByFourToggleVerticalColumn secondColumn second) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourTogglePair_fineRelated first second firstColumn secondColumn hfirst hsecond

/--
[sixVertexFourByFourAudited_selectedColumns_constant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleFibre.lean)
-/
@[path]
private lemma sixVertexFourByFourAudited_selectedColumns_constant_eq
  {p : SixVertexFourByFourAuditedHorizontalParameters}
  {firstSeam secondSeam : Fin 4} :
-- imply
  SixVertexFourByFourAuditedSelectedColumnsConstantStatement p firstSeam secondSeam := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAudited_selectedColumns_constant p firstSeam secondSeam

/--
[sixVertexFourByFourAuditedParamMatching_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleFibre.lean)
-/
@[path]
private lemma sixVertexFourByFourAuditedParamMatching_valid_eq
  {p : SixVertexFourByFourAuditedHorizontalParameters}
  {firstSeam secondSeam : Fin 4} :
-- imply
  SixVertexFourByFourAuditedParamMatchingStatement p firstSeam secondSeam := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAuditedParamMatching_valid p firstSeam secondSeam

/--
[sixVertexFourByFourAuditedCoordinateRows_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleFibre.lean)
-/
@[path]
private lemma sixVertexFourByFourAuditedCoordinateRows_invariant_eq
  {c : SixVertexFourByFourAuditedCoordinates} :
-- imply
  SixVertexFourByFourAuditedCoordinateRowsInvariant c := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAuditedCoordinateRows_invariant c

/--
[sixVertexFourByFour_iceRule_of_rowIce](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleFibre.lean)
-/
@[path]
private lemma sixVertexFourByFour_iceRule_of_rowIce_eq
  {omega : SixVertexArrows sixVertexFourByFourTorus}
-- given
  (hrow : forall y, svHorizontalIce sixVertexFourByFourTorus.width_pos (svTorusVerticalRows sixVertexFourByFourTorus omega (SixVertexArrows.cyclicPred sixVertexFourByFourTorus.height_pos y)) (svTorusVerticalRows sixVertexFourByFourTorus omega y) (svTorusHorizontalRows sixVertexFourByFourTorus omega y)) :
-- imply
  omega.IceRule := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFour_iceRule_of_rowIce omega hrow

/--
[sixVertexFourByFourAuditedCoordinateFirst_rowIce](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleFibre.lean)
-/
@[path]
private lemma sixVertexFourByFourAuditedCoordinateFirst_rowIce_eq
  {c : SixVertexFourByFourAuditedCoordinates}
  {y : Fin 4} :
-- imply
  let p := sixVertexFourByFourAuditedCoordinateParameters c svHorizontalIce sixVertexFourByFourTorus.width_pos (sixVertexFourByFourAuditedParamVerticalRowsFirst p c.firstSeam (SixVertexArrows.cyclicPred sixVertexFourByFourTorus.height_pos y)) (sixVertexFourByFourAuditedParamVerticalRowsFirst p c.firstSeam y) (sixVertexFourByFourAuditedParamHorizontalRowsFirst p y) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAuditedCoordinateFirst_rowIce c y

/--
[sixVertexFourByFourAuditedCoordinateSecond_rowIce](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleFibre.lean)
-/
@[path]
private lemma sixVertexFourByFourAuditedCoordinateSecond_rowIce_eq
  {c : SixVertexFourByFourAuditedCoordinates}
  {y : Fin 4} :
-- imply
  let p := sixVertexFourByFourAuditedCoordinateParameters c svHorizontalIce sixVertexFourByFourTorus.width_pos (sixVertexFourByFourAuditedParamVerticalRowsSecond p c.secondSeam (SixVertexArrows.cyclicPred sixVertexFourByFourTorus.height_pos y)) (sixVertexFourByFourAuditedParamVerticalRowsSecond p c.secondSeam y) (sixVertexFourByFourAuditedParamHorizontalRowsSecond p y) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAuditedCoordinateSecond_rowIce c y

/--
[sixVertexFourByFourAuditedCoordinateSourcePair_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleFibre.lean)
-/
@[path]
private lemma sixVertexFourByFourAuditedCoordinateSourcePair_valid_eq
  {c : SixVertexFourByFourAuditedCoordinates} :
-- imply
  SixVertexFourByFourAuditedCoordinateSourcePairValid c := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourAuditedCoordinateSourcePair_valid c


-- created on 2026-10-23
