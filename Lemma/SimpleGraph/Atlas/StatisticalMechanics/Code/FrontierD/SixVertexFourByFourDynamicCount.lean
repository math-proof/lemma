import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourDynamicCount.Part2
open Finset StatMech StatMech.FrontierD


/--
[sixVertexFourGradeCountExecutable_eq_cycleTuple](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourDynamicCount.lean)
-/
@[path]
private lemma sixVertexFourGradeCountExecutable_eq_cycleTuple_eq
  {sector : Fin 5}
  {totalC : Nat} :
-- imply
  sixVertexMarkedSectorRowCycleGradeCountExecutable sixVertexFourByFourTorus sector totalC = sixVertexFourCycleTupleGradeCount sector totalC := by
-- proof
  apply StatMech.FrontierD.sixVertexFourGradeCountExecutable_eq_cycleTuple sector totalC

/--
[sixVertexFourCycleTupleGradeCount_eq_rows](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourDynamicCount.lean)
-/
@[path]
private lemma sixVertexFourCycleTupleGradeCount_eq_rows_eq
  {sector : Fin 5}
  {totalC : Nat} :
-- imply
  sixVertexFourCycleTupleGradeCount sector totalC = sixVertexFourCycleRowGradeCount sector totalC := by
-- proof
  apply StatMech.FrontierD.sixVertexFourCycleTupleGradeCount_eq_rows sector totalC

/--
[sixVertexFourGradeCountExecutable_eq_cycleRows](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourDynamicCount.lean)
-/
@[path]
private lemma sixVertexFourGradeCountExecutable_eq_cycleRows_eq
  {sector : Fin 5}
  {totalC : Nat} :
-- imply
  sixVertexMarkedSectorRowCycleGradeCountExecutable sixVertexFourByFourTorus sector totalC = sixVertexFourCycleRowGradeCount sector totalC := by
-- proof
  apply StatMech.FrontierD.sixVertexFourGradeCountExecutable_eq_cycleRows sector totalC

/--
[sixVertexFourVerticalRowsTotalC_eq_twoStepGrades](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourDynamicCount.lean)
-/
@[path]
private lemma sixVertexFourVerticalRowsTotalC_eq_twoStepGrades_eq
  {seam opposite middle0 middle2 : Fin 16} :
-- imply
  sixVertexVerticalRowsTotalC (T := sixVertexFourByFourTorus) ![ sixVertexFourRowOfIndex middle0, sixVertexFourRowOfIndex opposite, sixVertexFourRowOfIndex middle2, sixVertexFourRowOfIndex seam] = sixVertexFourTwoStepGrade seam middle0 opposite + sixVertexFourTwoStepGrade opposite middle2 seam := by
-- proof
  apply StatMech.FrontierD.sixVertexFourVerticalRowsTotalC_eq_twoStepGrades seam opposite middle0 middle2

/--
[sixVertexFourWitnessProduct_eq_twoStepWeights](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourDynamicCount.lean)
-/
@[path]
private lemma sixVertexFourWitnessProduct_eq_twoStepWeights_eq
  {seam opposite middle0 middle2 : Fin 16} :
-- imply
  (∏ j, sixVertexHorizontalTransitionWitnessCountExecutable (T := sixVertexFourByFourTorus) ![ sixVertexFourRowOfIndex middle0, sixVertexFourRowOfIndex opposite, sixVertexFourRowOfIndex middle2, sixVertexFourRowOfIndex seam] j) = sixVertexFourTwoStepWeight seam middle0 opposite * sixVertexFourTwoStepWeight opposite middle2 seam := by
-- proof
  apply StatMech.FrontierD.sixVertexFourWitnessProduct_eq_twoStepWeights seam opposite middle0 middle2

/--
[sixVertexFourCycleRowGradeCount_eq_indices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourDynamicCount.lean)
-/
@[path]
private lemma sixVertexFourCycleRowGradeCount_eq_indices_eq
  {sector : Fin 5}
  {totalC : Nat} :
-- imply
  sixVertexFourCycleRowGradeCount sector totalC = sixVertexFourCycleIndexGradeCountExpanded sector totalC := by
-- proof
  apply StatMech.FrontierD.sixVertexFourCycleRowGradeCount_eq_indices sector totalC

/--
[sixVertexFourGradeCountExecutable_eq_cycleIndicesExpanded](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourDynamicCount.lean)
-/
@[path]
private lemma sixVertexFourGradeCountExecutable_eq_cycleIndicesExpanded_eq
  {sector : Fin 5}
  {totalC : Nat} :
-- imply
  sixVertexMarkedSectorRowCycleGradeCountExecutable sixVertexFourByFourTorus sector totalC = sixVertexFourCycleIndexGradeCountExpanded sector totalC := by
-- proof
  apply StatMech.FrontierD.sixVertexFourGradeCountExecutable_eq_cycleIndicesExpanded sector totalC

/--
[sixVertexFourCycleIndexGradeCountExpanded_eq_factored](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourDynamicCount.lean)
-/
@[path]
private lemma sixVertexFourCycleIndexGradeCountExpanded_eq_factored_eq
  {sector : Fin 5}
  {totalC : Nat} :
-- imply
  sixVertexFourCycleIndexGradeCountExpanded sector totalC = sixVertexFourCycleIndexGradeCount sector totalC := by
-- proof
  apply StatMech.FrontierD.sixVertexFourCycleIndexGradeCountExpanded_eq_factored sector totalC

/--
[sixVertexFourGradeCountExecutable_eq_cycleIndices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourDynamicCount.lean)
-/
@[path]
private lemma sixVertexFourGradeCountExecutable_eq_cycleIndices_eq
  {sector : Fin 5}
  {totalC : Nat} :
-- imply
  sixVertexMarkedSectorRowCycleGradeCountExecutable sixVertexFourByFourTorus sector totalC = sixVertexFourCycleIndexGradeCount sector totalC := by
-- proof
  apply StatMech.FrontierD.sixVertexFourGradeCountExecutable_eq_cycleIndices sector totalC

/--
[sixVertexRowDistance_le_width](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourDynamicCount.lean)
-/
@[path]
private lemma sixVertexRowDistance_le_width_eq
  {N : Nat}
  {first second : SixVertexRow N} :
-- imply
  sixVertexRowDistance first second ≤ N := by
-- proof
  apply StatMech.FrontierD.sixVertexRowDistance_le_width first second

/--
[sixVertexFourTwoStepGrade_lt_nine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourDynamicCount.lean)
-/
@[path]
private lemma sixVertexFourTwoStepGrade_lt_nine_eq
  {start middle finish : Fin 16} :
-- imply
  sixVertexFourTwoStepGrade start middle finish < 9 := by
-- proof
  apply StatMech.FrontierD.sixVertexFourTwoStepGrade_lt_nine start middle finish

/--
[sixVertexFourTwoStepFactor_eq_countNat](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourDynamicCount.lean)
-/
@[path]
private lemma sixVertexFourTwoStepFactor_eq_countNat_eq
  {start finish : Fin 16}
  {grade : Nat} :
-- imply
  (∑ middle : Fin 16, if sixVertexFourTwoStepGrade start middle finish = grade then sixVertexFourTwoStepWeight start middle finish else 0) = sixVertexFourTwoStepCountNat start finish grade := by
-- proof
  apply StatMech.FrontierD.sixVertexFourTwoStepFactor_eq_countNat start finish grade

/--
[sixVertexFourTwoStepPairConvolution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourDynamicCount.lean)
-/
@[path]
private lemma sixVertexFourTwoStepPairConvolution_eq
  {seam opposite : Fin 16}
  {totalC : Nat} :
-- imply
  (∑ middle0 : Fin 16, ∑ middle2 : Fin 16, if sixVertexFourTwoStepGrade seam middle0 opposite + sixVertexFourTwoStepGrade opposite middle2 seam = totalC then sixVertexFourTwoStepWeight seam middle0 opposite * sixVertexFourTwoStepWeight opposite middle2 seam else 0) = ∑ grade : Fin (totalC + 1), sixVertexFourTwoStepCountNat seam opposite grade.val * sixVertexFourTwoStepCountNat opposite seam (totalC - grade.val) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourTwoStepPairConvolution seam opposite totalC

/--
[sixVertexFourCycleIndexGradeCount_eq_dynamic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourDynamicCount.lean)
-/
@[path]
private lemma sixVertexFourCycleIndexGradeCount_eq_dynamic_eq
  {sector : Fin 5}
  {totalC : Nat} :
-- imply
  sixVertexFourCycleIndexGradeCount sector totalC = sixVertexFourDynamicGradeCount sector totalC := by
-- proof
  apply StatMech.FrontierD.sixVertexFourCycleIndexGradeCount_eq_dynamic sector totalC

/--
[sixVertexFourGradeCountExecutable_eq_dynamic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourDynamicCount.lean)
-/
@[path]
private lemma sixVertexFourGradeCountExecutable_eq_dynamic_eq
  {sector : Fin 5}
  {totalC : Nat} :
-- imply
  sixVertexMarkedSectorRowCycleGradeCountExecutable sixVertexFourByFourTorus sector totalC = sixVertexFourDynamicGradeCount sector totalC := by
-- proof
  apply StatMech.FrontierD.sixVertexFourGradeCountExecutable_eq_dynamic sector totalC


-- created on 2026-10-23
