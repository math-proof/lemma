import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourPhysicalBranch.Part6
open Finset StatMech StatMech.FrontierD


/--
[sixVertexVerticalRowsTotalC_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourPhysicalBranch.lean)
-/
@[path]
private lemma sixVertexVerticalRowsTotalC_le_eq
  {T : EvenTorus}
  {vertical : Fin T.height → SixVertexRow T.width} :
-- imply
  sixVertexVerticalRowsTotalC vertical ≤ T.height * T.width := by
-- proof
  apply StatMech.FrontierD.sixVertexVerticalRowsTotalC_le vertical

/--
[sixVertexMarkedSectorRowCycleGradeCount_eq_zero_of_area_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourPhysicalBranch.lean)
-/
@[path]
private lemma sixVertexMarkedSectorRowCycleGradeCount_eq_zero_of_area_lt_eq
  {T : EvenTorus}
  {sector : Fin (T.width + 1)}
  {totalC : Nat}
-- given
  (hlarge : T.height * T.width < totalC) :
-- imply
  sixVertexMarkedSectorRowCycleGradeCount T sector totalC = 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexMarkedSectorRowCycleGradeCount_eq_zero_of_area_lt T sector totalC hlarge

/--
[sixVertexFourByFourRowCycleGradeCount_eq_nat](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourPhysicalBranch.lean)
-/
@[path]
private lemma sixVertexFourByFourRowCycleGradeCount_eq_nat_eq
  {sector : Fin 5}
  {totalC : Nat} :
-- imply
  sixVertexMarkedSectorRowCycleGradeCount sixVertexFourByFourTorus sector totalC = sixVertexFourByFourGradeCountNat sector totalC := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourRowCycleGradeCount_eq_nat sector totalC

/--
[sixVertexFourByFourRowCyclePairGradeCount_eq_nat](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourPhysicalBranch.lean)
-/
@[path]
private lemma sixVertexFourByFourRowCyclePairGradeCount_eq_nat_eq
  {left right : Fin 5}
  {totalC : Nat} :
-- imply
  sixVertexMarkedSectorRowCyclePairGradeCount sixVertexFourByFourTorus left right totalC = sixVertexFourByFourPairGradeCountNat left right totalC := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourRowCyclePairGradeCount_eq_nat left right totalC

/--
[sixVertexMarkedSectorRowCycleDiagonalGradeCount_eq_nat](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourPhysicalBranch.lean)
-/
@[path]
private lemma sixVertexMarkedSectorRowCycleDiagonalGradeCount_eq_nat_eq
  {T : EvenTorus}
  {sector : Fin (T.width + 1)}
  {totalC : Nat} :
-- imply
  sixVertexMarkedSectorRowCycleDiagonalGradeCount T sector totalC = if totalC % 2 = 0 then sixVertexMarkedSectorRowCycleGradeCount T sector (totalC / 2) else 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexMarkedSectorRowCycleDiagonalGradeCount_eq_nat T sector totalC

/--
[sixVertexFourByFourDiagonalGradeCount_eq_nat](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourPhysicalBranch.lean)
-/
@[path]
private lemma sixVertexFourByFourDiagonalGradeCount_eq_nat_eq
  {sector : Fin 5}
  {totalC : Nat} :
-- imply
  sixVertexMarkedSectorRowCycleDiagonalGradeCount sixVertexFourByFourTorus sector totalC = sixVertexFourByFourDiagonalGradeCountNat sector totalC := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourDiagonalGradeCount_eq_nat sector totalC

/--
[sixVertexFourByFourOffDiagonalGradeCount_eq_nat](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourPhysicalBranch.lean)
-/
@[path]
private lemma sixVertexFourByFourOffDiagonalGradeCount_eq_nat_eq
  {sector : Fin 5}
  {totalC : Nat} :
-- imply
  Nat.card {target : SixVertexPhysicalRowCycleOffDiagonalTarget sixVertexFourByFourTorus sector // sixVertexPhysicalRowCyclePairTotalC target.1 = totalC} = sixVertexFourByFourOffDiagonalGradeCountNat sector totalC := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourOffDiagonalGradeCount_eq_nat sector totalC

/--
[sixVertexFourByFour_middleOne_gradeCapacity_certificate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourPhysicalBranch.lean)
-/
@[path]
private lemma sixVertexFourByFour_middleOne_gradeCapacity_certificate_eq :
-- imply
  ∀ totalC : Fin 33, sixVertexFourByFourPairGradeCountNat 0 2 totalC.val ≤ sixVertexFourByFourOffDiagonalGradeCountNat 1 totalC.val := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFour_middleOne_gradeCapacity_certificate

/--
[sixVertexFourByFour_middleTwo_gradeCapacity_certificate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourPhysicalBranch.lean)
-/
@[path]
private lemma sixVertexFourByFour_middleTwo_gradeCapacity_certificate_eq :
-- imply
  ∀ totalC : Fin 33, sixVertexFourByFourPairGradeCountNat 1 3 totalC.val ≤ sixVertexFourByFourOffDiagonalGradeCountNat 2 totalC.val := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFour_middleTwo_gradeCapacity_certificate

/--
[sixVertexFourByFourSectorOne_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourPhysicalBranch.lean)
-/
@[path]
private lemma sixVertexFourByFourSectorOne_pos_eq :
-- imply
  0 < sixVertexFourByFourSectorOne.val := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourSectorOne_pos

/--
[sixVertexFourByFourSectorOne_lt_width](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourPhysicalBranch.lean)
-/
@[path]
private lemma sixVertexFourByFourSectorOne_lt_width_eq :
-- imply
  sixVertexFourByFourSectorOne.val < sixVertexFourByFourTorus.width := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourSectorOne_lt_width

/--
[sixVertexFourByFourSectorTwo_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourPhysicalBranch.lean)
-/
@[path]
private lemma sixVertexFourByFourSectorTwo_pos_eq :
-- imply
  0 < sixVertexFourByFourSectorTwo.val := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourSectorTwo_pos

/--
[sixVertexFourByFourSectorTwo_lt_width](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourPhysicalBranch.lean)
-/
@[path]
private lemma sixVertexFourByFourSectorTwo_lt_width_eq :
-- imply
  sixVertexFourByFourSectorTwo.val < sixVertexFourByFourTorus.width := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourSectorTwo_lt_width

/--
[sixVertexFourByFourPhysicalSourceGradeCount_middleOne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourPhysicalBranch.lean)
-/
@[path]
private lemma sixVertexFourByFourPhysicalSourceGradeCount_middleOne_eq
  {totalC : Nat} :
-- imply
  Nat.card {source : SixVertexPhysicalRowCycleSource sixVertexFourByFourTorus sixVertexFourByFourSectorOne sixVertexFourByFourSectorOne_pos sixVertexFourByFourSectorOne_lt_width // sixVertexPhysicalRowCyclePairTotalC source = totalC} = sixVertexFourByFourPairGradeCountNat 0 2 totalC := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourPhysicalSourceGradeCount_middleOne totalC

/--
[sixVertexFourByFourPhysicalSourceGradeCount_middleTwo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourPhysicalBranch.lean)
-/
@[path]
private lemma sixVertexFourByFourPhysicalSourceGradeCount_middleTwo_eq
  {totalC : Nat} :
-- imply
  Nat.card {source : SixVertexPhysicalRowCycleSource sixVertexFourByFourTorus sixVertexFourByFourSectorTwo sixVertexFourByFourSectorTwo_pos sixVertexFourByFourSectorTwo_lt_width // sixVertexPhysicalRowCyclePairTotalC source = totalC} = sixVertexFourByFourPairGradeCountNat 1 3 totalC := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourPhysicalSourceGradeCount_middleTwo totalC

/--
[sixVertexFourByFourRowCycleTotalC_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourPhysicalBranch.lean)
-/
@[path]
private lemma sixVertexFourByFourRowCycleTotalC_le_eq
  {sector : Fin 5}
  {rows : SixVertexMarkedSectorRowCycle sixVertexFourByFourTorus sector} :
-- imply
  sixVertexMarkedSectorRowCycleTotalC rows ≤ 16 := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourRowCycleTotalC_le rows

/--
[sixVertexFourByFourPhysicalSourceTotalC_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourPhysicalBranch.lean)
-/
@[path]
private lemma sixVertexFourByFourPhysicalSourceTotalC_le_eq
  {middle : Fin 5}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < sixVertexFourByFourTorus.width}
  {source : SixVertexPhysicalRowCycleSource sixVertexFourByFourTorus middle hmiddle_pos hmiddle_lt} :
-- imply
  sixVertexPhysicalRowCyclePairTotalC source ≤ 32 := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourPhysicalSourceTotalC_le source

/--
[sixVertexFourByFourMiddleOneExactGradeCapacity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourPhysicalBranch.lean)
-/
@[path]
private lemma sixVertexFourByFourMiddleOneExactGradeCapacity_eq :
-- imply
  SixVertexPhysicalRowCycleExactGradeCapacity sixVertexFourByFourTorus sixVertexFourByFourSectorOne sixVertexFourByFourSectorOne_pos sixVertexFourByFourSectorOne_lt_width := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourMiddleOneExactGradeCapacity

/--
[sixVertexFourByFourMiddleTwoExactGradeCapacity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourPhysicalBranch.lean)
-/
@[path]
private lemma sixVertexFourByFourMiddleTwoExactGradeCapacity_eq :
-- imply
  SixVertexPhysicalRowCycleExactGradeCapacity sixVertexFourByFourTorus sixVertexFourByFourSectorTwo sixVertexFourByFourSectorTwo_pos sixVertexFourByFourSectorTwo_lt_width := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourMiddleTwoExactGradeCapacity

/--
[sixVertexFourByFourPhysicalPairedBranchEmbeddings_allSectors](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourPhysicalBranch.lean)
-/
@[path]
private lemma sixVertexFourByFourPhysicalPairedBranchEmbeddings_allSectors_eq
  {n : Nat}
-- given
  (hn0 : 0 < n)
  (hn4 : n < 4) :
-- imply
  Nonempty (SixVertexConfigurationPhysicalPairedBranchEmbeddings sixVertexFourByFourTorus ⟨n, by norm_num [sixVertexFourByFourTorus]; omega⟩ hn0 hn4) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourPhysicalPairedBranchEmbeddings_allSectors n hn0 hn4


-- created on 2026-10-23
