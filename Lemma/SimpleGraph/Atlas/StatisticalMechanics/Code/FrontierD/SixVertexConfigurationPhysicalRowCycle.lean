import Mathlib
import sympy.Basic
import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalRowCycle.Part11
open Finset StatMech StatMech.FrontierD


/--
[sixVertexIceRule_iff_horizontalRowTransitions](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPhysicalRowCycle.lean)
-/
@[path]
private lemma sixVertexIceRule_iff_horizontalRowTransitions_eq
  {T : EvenTorus}
  {omega : SixVertexArrows T} :
-- imply
  omega.IceRule ↔ forall j : Fin T.height, svHorizontalIce T.width_pos (svTorusVerticalRows T omega (SixVertexArrows.cyclicPred T.height_pos j)) (svTorusVerticalRows T omega j) (svTorusHorizontalRows T omega j) := by
-- proof
  apply StatMech.FrontierD.sixVertexIceRule_iff_horizontalRowTransitions omega

/--
[sixVertexArrows_isCType_iff_verticalRow_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPhysicalRowCycle.lean)
-/
@[path]
private lemma sixVertexArrows_isCType_iff_verticalRow_ne_eq
  {T : EvenTorus}
  {omega : SixVertexArrows T}
  {i : Fin T.width}
  {j : Fin T.height}
-- given
  (homega : omega.IceRule) :
-- imply
  omega.IsCType (i, j) ↔ svTorusVerticalRows T omega (SixVertexArrows.cyclicPred T.height_pos j) i ≠ svTorusVerticalRows T omega j i := by
-- proof
  apply StatMech.FrontierD.sixVertexArrows_isCType_iff_verticalRow_ne omega homega i j

/--
[sixVertexTorusCTypeCount_eq_rowCycleTotalC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPhysicalRowCycle.lean)
-/
@[path]
private lemma sixVertexTorusCTypeCount_eq_rowCycleTotalC_eq
  {T : EvenTorus}
  {sector : Fin (T.width + 1)}
  {omega : SixVertexMarkedSectorConfiguration T sector} :
-- imply
  sixVertexTorusCTypeCount omega.1 = sixVertexMarkedSectorRowCycleTotalC (sixVertexMarkedSectorConfigurationEquivRowCycle T sector omega) := by
-- proof
  apply StatMech.FrontierD.sixVertexTorusCTypeCount_eq_rowCycleTotalC omega

/--
[card_sixVertexMarkedSectorRowCycleGradeFiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPhysicalRowCycle.lean)
-/
@[path]
private lemma card_sixVertexMarkedSectorRowCycleGradeFiber_eq
  {T : EvenTorus}
  {sector : Fin (T.width + 1)}
  {totalC : Nat} :
-- imply
  Fintype.card {rows : SixVertexMarkedSectorRowCycle T sector // sixVertexMarkedSectorRowCycleTotalC rows = totalC} = sixVertexMarkedSectorRowCycleGradeCount T sector totalC := by
-- proof
  apply StatMech.FrontierD.card_sixVertexMarkedSectorRowCycleGradeFiber T sector totalC

/--
[natCard_natGradedPairFiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPhysicalRowCycle.lean)
-/
@[path]
private lemma natCard_natGradedPairFiber_eq
  [Finite A]
  [Finite B]
  {gradeA : A → Nat}
  {gradeB : B → Nat}
  {total : Nat} :
-- imply
  Nat.card {pair : A × B // gradeA pair.1 + gradeB pair.2 = total} = ∑ k : Fin (total + 1), Nat.card {a : A // gradeA a = k.val} * Nat.card {b : B // gradeB b = total - k.val} := by
-- proof
  apply StatMech.FrontierD.natCard_natGradedPairFiber gradeA gradeB total

/--
[card_sixVertexMarkedSectorRowCyclePairGradeFiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPhysicalRowCycle.lean)
-/
@[path]
private lemma card_sixVertexMarkedSectorRowCyclePairGradeFiber_eq
  {T : EvenTorus}
  {left right : Fin (T.width + 1)}
  {totalC : Nat} :
-- imply
  Fintype.card {pair : SixVertexMarkedSectorRowCycle T left × SixVertexMarkedSectorRowCycle T right // sixVertexMarkedSectorRowCyclePairTotalC pair = totalC} = sixVertexMarkedSectorRowCyclePairGradeCount T left right totalC := by
-- proof
  apply StatMech.FrontierD.card_sixVertexMarkedSectorRowCyclePairGradeFiber T left right totalC

/--
[sixVertexMarkedSectorRowCyclePairGradeCount_eq_convolution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPhysicalRowCycle.lean)
-/
@[path]
private lemma sixVertexMarkedSectorRowCyclePairGradeCount_eq_convolution_eq
  {T : EvenTorus}
  {left right : Fin (T.width + 1)}
  {totalC : Nat} :
-- imply
  sixVertexMarkedSectorRowCyclePairGradeCount T left right totalC = ∑ k : Fin (totalC + 1), sixVertexMarkedSectorRowCycleGradeCount T left k.val * sixVertexMarkedSectorRowCycleGradeCount T right (totalC - k.val) := by
-- proof
  apply StatMech.FrontierD.sixVertexMarkedSectorRowCyclePairGradeCount_eq_convolution T left right totalC

/--
[card_sixVertexMarkedSectorRowCycleDiagonalGradeFiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPhysicalRowCycle.lean)
-/
@[path]
private lemma card_sixVertexMarkedSectorRowCycleDiagonalGradeFiber_eq
  {T : EvenTorus}
  {sector : Fin (T.width + 1)}
  {totalC : Nat} :
-- imply
  Fintype.card {rows : SixVertexMarkedSectorRowCycle T sector // 2 * sixVertexMarkedSectorRowCycleTotalC rows = totalC} = sixVertexMarkedSectorRowCycleDiagonalGradeCount T sector totalC := by
-- proof
  apply StatMech.FrontierD.card_sixVertexMarkedSectorRowCycleDiagonalGradeFiber T sector totalC

/--
[sixVertexPhysicalSourceEquivRowCycles_totalC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPhysicalRowCycle.lean)
-/
@[path]
private lemma sixVertexPhysicalSourceEquivRowCycles_totalC_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {source : SixVertexConfigurationPhysicalSource T middle hmiddle_pos hmiddle_lt} :
-- imply
  sixVertexPhysicalRowCyclePairTotalC (sixVertexPhysicalSourceEquivRowCycles source) = sixVertexConfigurationPairTotalCPhysical source := by
-- proof
  apply StatMech.FrontierD.sixVertexPhysicalSourceEquivRowCycles_totalC source

/--
[sixVertexPhysicalTargetEquivRowCycles_totalC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPhysicalRowCycle.lean)
-/
@[path]
private lemma sixVertexPhysicalTargetEquivRowCycles_totalC_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {target : SixVertexConfigurationPhysicalTarget T middle} :
-- imply
  sixVertexPhysicalRowCyclePairTotalC (sixVertexPhysicalTargetEquivRowCycles target) = sixVertexConfigurationPairTotalCPhysical target := by
-- proof
  apply StatMech.FrontierD.sixVertexPhysicalTargetEquivRowCycles_totalC target

/--
[sixVertexPhysicalTargetEquivRowCycles_symm_totalC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPhysicalRowCycle.lean)
-/
@[path]
private lemma sixVertexPhysicalTargetEquivRowCycles_symm_totalC_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {target : SixVertexPhysicalRowCycleTarget T middle} :
-- imply
  sixVertexConfigurationPairTotalCPhysical (sixVertexPhysicalTargetEquivRowCycles.symm target) = sixVertexPhysicalRowCyclePairTotalC target := by
-- proof
  apply StatMech.FrontierD.sixVertexPhysicalTargetEquivRowCycles_symm_totalC target

/--
[sixVertexPhysicalRowCycleOffDiagonal_branches_distinct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPhysicalRowCycle.lean)
-/
@[path]
private lemma sixVertexPhysicalRowCycleOffDiagonal_branches_distinct_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {target : SixVertexPhysicalRowCycleOffDiagonalTarget T middle} :
-- imply
  sixVertexPhysicalRowCycleOffDiagonalForget target ≠ sixVertexPhysicalRowCycleOffDiagonalSwap target := by
-- proof
  apply StatMech.FrontierD.sixVertexPhysicalRowCycleOffDiagonal_branches_distinct target

/--
[card_sixVertexPhysicalRowCycleOffDiagonalGradeFiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPhysicalRowCycle.lean)
-/
@[path]
private lemma card_sixVertexPhysicalRowCycleOffDiagonalGradeFiber_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {totalC : Nat} :
-- imply
  Fintype.card {target : SixVertexPhysicalRowCycleOffDiagonalTarget T middle // sixVertexPhysicalRowCyclePairTotalC target.1 = totalC} = sixVertexMarkedSectorRowCyclePairGradeCount T middle middle totalC - sixVertexMarkedSectorRowCycleDiagonalGradeCount T middle totalC := by
-- proof
  apply StatMech.FrontierD.card_sixVertexPhysicalRowCycleOffDiagonalGradeFiber T middle totalC

/--
[sixVertexPhysicalRowCycleOffDiagonalSwap_totalC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPhysicalRowCycle.lean)
-/
@[path]
private lemma sixVertexPhysicalRowCycleOffDiagonalSwap_totalC_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {target : SixVertexPhysicalRowCycleOffDiagonalTarget T middle} :
-- imply
  sixVertexPhysicalRowCyclePairTotalC (sixVertexPhysicalRowCycleOffDiagonalSwap target) = sixVertexPhysicalRowCyclePairTotalC target.1 := by
-- proof
  apply StatMech.FrontierD.sixVertexPhysicalRowCycleOffDiagonalSwap_totalC target


-- created on 2026-10-23
