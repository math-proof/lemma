import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalCompletionBigrade
open Finset StatMech StatMech.FrontierD


/--
[sixVertexCheckerHorizontalZeroCount_eq_horizontal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalCompletionBigrade.lean)
-/
@[path]
private lemma sixVertexCheckerHorizontalZeroCount_eq_horizontal_eq
  {T : EvenTorus}
  {omega : SixVertexArrows T} :
-- imply
  sixVertexCheckerHorizontalZeroCount omega = sixVertexHorizontalZeroCount omega.horizontal := by
-- proof
  apply StatMech.FrontierD.sixVertexCheckerHorizontalZeroCount_eq_horizontal omega

/--
[sixVertexCheckerHorizontalNontransitionCount_eq_horizontal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalCompletionBigrade.lean)
-/
@[path]
private lemma sixVertexCheckerHorizontalNontransitionCount_eq_horizontal_eq
  {T : EvenTorus}
  {omega : SixVertexArrows T} :
-- imply
  sixVertexCheckerHorizontalNontransitionCount omega = sixVertexHorizontalNontransitionCount omega.horizontal := by
-- proof
  apply StatMech.FrontierD.sixVertexCheckerHorizontalNontransitionCount_eq_horizontal omega

/--
[sixVertexConfigurationPairBigrade_eq_horizontalPairBigrade](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalCompletionBigrade.lean)
-/
@[path]
private lemma sixVertexConfigurationPairBigrade_eq_horizontalPairBigrade_eq
  {T : EvenTorus}
  {left right : Fin (T.width + 1)}
  {pair : SixVertexMarkedSectorConfiguration T left × SixVertexMarkedSectorConfiguration T right} :
-- imply
  sixVertexConfigurationPairBigrade pair = sixVertexHorizontalPairBigrade (pair.1.1.horizontal, pair.2.1.horizontal) := by
-- proof
  apply StatMech.FrontierD.sixVertexConfigurationPairBigrade_eq_horizontalPairBigrade pair

/--
[card_sixVertexConfigurationPairBigradeFiber_eq_horizontalCompletions](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalCompletionBigrade.lean)
-/
@[path]
private lemma card_sixVertexConfigurationPairBigradeFiber_eq_horizontalCompletions_eq
  {T : EvenTorus}
  {left right : Fin (T.width + 1)}
  {grade : Nat × Nat} :
-- imply
  Fintype.card {pair : SixVertexMarkedSectorConfiguration T left × SixVertexMarkedSectorConfiguration T right // sixVertexConfigurationPairBigrade pair = grade} = ∑ horizontal : {horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T // sixVertexHorizontalPairBigrade horizontal = grade}, Fintype.card (SixVertexHorizontalSectorCompletion T left horizontal.1.1) * Fintype.card (SixVertexHorizontalSectorCompletion T right horizontal.1.2) := by
-- proof
  apply StatMech.FrontierD.card_sixVertexConfigurationPairBigradeFiber_eq_horizontalCompletions T left right grade

/--
[sixVertexVerticalCompletionSeamRow_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalCompletionBigrade.lean)
-/
@[path]
private lemma sixVertexVerticalCompletionSeamRow_injective_eq
  {T : EvenTorus}
  {horizontal : SixVertexHorizontalField T} :
-- imply
  Function.Injective (sixVertexVerticalCompletionSeamRow (T := T) (horizontal := horizontal)) := by
-- proof
  apply StatMech.FrontierD.sixVertexVerticalCompletionSeamRow_injective

/--
[sixVertexVerticalColumnCompletionAtSeam_subsingleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalCompletionBigrade.lean)
-/
@[path]
private lemma sixVertexVerticalColumnCompletionAtSeam_subsingleton_eq
  {T : EvenTorus}
  {horizontal : SixVertexHorizontalField T}
  {i : Fin T.width}
  {seam : Bool} :
-- imply
  Subsingleton (SixVertexVerticalColumnCompletionAtSeam T horizontal i seam) := by
-- proof
  apply StatMech.FrontierD.sixVertexVerticalColumnCompletionAtSeam_subsingleton i seam

/--
[card_sixVertexHorizontalSectorCompletion_eq_sum_columnFibers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalCompletionBigrade.lean)
-/
@[path]
private lemma card_sixVertexHorizontalSectorCompletion_eq_sum_columnFibers_eq
  {T : EvenTorus}
  {sector : Fin (T.width + 1)}
-- given
  (horizontal : SixVertexHorizontalField T) :
-- imply
  Fintype.card (SixVertexHorizontalSectorCompletion T sector horizontal) = ∑ row : SixVertexSector T.width sector.val, ∏ i : Fin T.width, Fintype.card (SixVertexVerticalColumnCompletionAtSeam T horizontal i (sixVertexSectorRow row i)) := by
-- proof
  apply StatMech.FrontierD.card_sixVertexHorizontalSectorCompletion_eq_sum_columnFibers T sector horizontal

/--
[sixVertexHorizontalForcedTrueColumns_subset_trueAllowed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalCompletionBigrade.lean)
-/
@[path]
private lemma sixVertexHorizontalForcedTrueColumns_subset_trueAllowed_eq
  {T : EvenTorus}
-- given
  (horizontal : SixVertexHorizontalField T) :
-- imply
  sixVertexHorizontalForcedTrueColumns horizontal ⊆ sixVertexHorizontalTrueAllowedColumns horizontal := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalForcedTrueColumns_subset_trueAllowed horizontal

/--
[sixVertexHorizontalColumnSeamAllowed_false_or_true](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalCompletionBigrade.lean)
-/
@[path]
private lemma sixVertexHorizontalColumnSeamAllowed_false_or_true_eq
  {T : EvenTorus}
  {horizontal : SixVertexHorizontalField T}
  {completion : SixVertexVerticalCompletion T horizontal}
  {i : Fin T.width} :
-- imply
  sixVertexHorizontalColumnSeamAllowed horizontal i false \/ sixVertexHorizontalColumnSeamAllowed horizontal i true := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalColumnSeamAllowed_false_or_true completion i

/--
[sixVertexHorizontalAdmissibleSeamRow_iff_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalCompletionBigrade.lean)
-/
@[path]
private lemma sixVertexHorizontalAdmissibleSeamRow_iff_subset_eq
  {T : EvenTorus}
  {horizontal : SixVertexHorizontalField T}
  {completion : SixVertexVerticalCompletion T horizontal}
  {sector : Fin (T.width + 1)}
  {row : SixVertexSector T.width sector.val} :
-- imply
  Nonempty ((i : Fin T.width) -> SixVertexVerticalColumnCompletionAtSeam T horizontal i (sixVertexSectorRow row i)) <-> sixVertexHorizontalForcedTrueColumns horizontal ⊆ row.1 /\ row.1 ⊆ sixVertexHorizontalTrueAllowedColumns horizontal := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalAdmissibleSeamRow_iff_subset completion sector row

/--
[card_sixVertexHorizontalSectorCompletion_eq_choose](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalCompletionBigrade.lean)
-/
@[path]
private lemma card_sixVertexHorizontalSectorCompletion_eq_choose_eq
  {T : EvenTorus}
  {horizontal : SixVertexHorizontalField T}
  {completion : SixVertexVerticalCompletion T horizontal}
  {sector : Fin (T.width + 1)} :
-- imply
  Fintype.card (SixVertexHorizontalSectorCompletion T sector horizontal) = if (sixVertexHorizontalForcedTrueColumns horizontal).card <= sector.val then Nat.choose ((sixVertexHorizontalTrueAllowedColumns horizontal).card - (sixVertexHorizontalForcedTrueColumns horizontal).card) (sector.val - (sixVertexHorizontalForcedTrueColumns horizontal).card) else 0 := by
-- proof
  apply StatMech.FrontierD.card_sixVertexHorizontalSectorCompletion_eq_choose completion sector

/--
[card_sixVertexHorizontalSectorCompletion_eq_chooseCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalCompletionBigrade.lean)
-/
@[path]
private lemma card_sixVertexHorizontalSectorCompletion_eq_chooseCount_eq
  {T : EvenTorus}
  {sector : Fin (T.width + 1)}
-- given
  (horizontal : SixVertexHorizontalField T) :
-- imply
  Fintype.card (SixVertexHorizontalSectorCompletion T sector horizontal) = sixVertexHorizontalSectorCompletionChooseCount T sector horizontal := by
-- proof
  apply StatMech.FrontierD.card_sixVertexHorizontalSectorCompletion_eq_chooseCount T sector horizontal

/--
[sixVertexHorizontalSectorCompletionChooseCount_pos_of_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalCompletionBigrade.lean)
-/
@[path]
private lemma sixVertexHorizontalSectorCompletionChooseCount_pos_of_nonempty_eq
  {T : EvenTorus}
  {sector : Fin (T.width + 1)}
-- given
  (horizontal : SixVertexHorizontalField T)
  (hnonempty : Nonempty (SixVertexHorizontalSectorCompletion T sector horizontal)) :
-- imply
  0 < sixVertexHorizontalSectorCompletionChooseCount T sector horizontal := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalSectorCompletionChooseCount_pos_of_nonempty T sector horizontal hnonempty

/--
[sixVertexHorizontalSectorCompletionChooseCount_eq_zero_of_isEmpty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalCompletionBigrade.lean)
-/
@[path]
private lemma sixVertexHorizontalSectorCompletionChooseCount_eq_zero_of_isEmpty_eq
  {T : EvenTorus}
  {sector : Fin (T.width + 1)}
-- given
  (horizontal : SixVertexHorizontalField T)
  (hempty : IsEmpty (SixVertexHorizontalSectorCompletion T sector horizontal)) :
-- imply
  sixVertexHorizontalSectorCompletionChooseCount T sector horizontal = 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalSectorCompletionChooseCount_eq_zero_of_isEmpty T sector horizontal hempty

/--
[card_sixVertexConfigurationPairBigradeFiber_eq_chooseSums](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalCompletionBigrade.lean)
-/
@[path]
private lemma card_sixVertexConfigurationPairBigradeFiber_eq_chooseSums_eq
  {T : EvenTorus}
  {left right : Fin (T.width + 1)}
  {grade : Nat × Nat} :
-- imply
  Fintype.card {pair : SixVertexMarkedSectorConfiguration T left × SixVertexMarkedSectorConfiguration T right // sixVertexConfigurationPairBigrade pair = grade} = ∑ horizontal : {horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T // sixVertexHorizontalPairBigrade horizontal = grade}, sixVertexHorizontalSectorCompletionChooseCount T left horizontal.1.1 * sixVertexHorizontalSectorCompletionChooseCount T right horizontal.1.2 := by
-- proof
  apply StatMech.FrontierD.card_sixVertexConfigurationPairBigradeFiber_eq_chooseSums T left right grade

/--
[configurationBigradeFibers_iff_horizontalChooseBigradeFibers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalCompletionBigrade.lean)
-/
@[path]
private lemma configurationBigradeFibers_iff_horizontalChooseBigradeFibers_eq
  {T : EvenTorus}
  {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)} :
-- imply
  SixVertexConfigurationPairBigradeFiberDominates T sourceLeft sourceRight targetLeft targetRight <-> SixVertexHorizontalChooseBigradeFiberDominates T sourceLeft sourceRight targetLeft targetRight := by
-- proof
  apply StatMech.FrontierD.configurationBigradeFibers_iff_horizontalChooseBigradeFibers T sourceLeft sourceRight targetLeft targetRight


-- created on 2026-10-23
