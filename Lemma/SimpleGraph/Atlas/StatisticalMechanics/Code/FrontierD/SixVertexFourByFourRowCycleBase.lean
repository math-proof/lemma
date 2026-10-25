import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourRowCycleBase.Part5
open StatMech StatMech.FrontierD


/--
[sixVertexFourRowOfIndex_bijective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourRowCycleBase.lean)
-/
@[path]
private lemma sixVertexFourRowOfIndex_bijective_eq :
-- imply
  Function.Bijective sixVertexFourRowOfIndex := by
-- proof
  apply StatMech.FrontierD.sixVertexFourRowOfIndex_bijective

/--
[sixVertexFourRowIndexEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourRowCycleBase.lean)
-/
@[path]
private lemma sixVertexFourRowIndexEquiv_apply_eq
  {index : Fin 16} :
-- imply
  sixVertexFourRowIndexEquiv index = sixVertexFourRowOfIndex index := by
-- proof
  apply StatMech.FrontierD.sixVertexFourRowIndexEquiv_apply index

/--
[sixVertexFourHorizontalTransitionCount_certificate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourRowCycleBase.lean)
-/
@[path]
private lemma sixVertexFourHorizontalTransitionCount_certificate_eq :
-- imply
  ∀ previous current : Fin 16, sixVertexHorizontalTransitionCountExecutable (T := sixVertexFourByFourTorus) (sixVertexFourRowOfIndex previous) (sixVertexFourRowOfIndex current) = sixVertexFourHorizontalTransitionCount previous current := by
-- proof
  apply StatMech.FrontierD.sixVertexFourHorizontalTransitionCount_certificate

/--
[sixVertexFourByFourGradeCountExecutable_eq_tuple](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourRowCycleBase.lean)
-/
@[path]
private lemma sixVertexFourByFourGradeCountExecutable_eq_tuple_eq
  {sector : Fin 5}
  {totalC : Nat} :
-- imply
  sixVertexMarkedSectorRowCycleGradeCountExecutable sixVertexFourByFourTorus sector totalC = sixVertexFourByFourTupleGradeCountExecutable sector totalC := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourGradeCountExecutable_eq_tuple sector totalC

/--
[sixVertexFourByFourTupleGradeCountExecutable_eq_rows](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourRowCycleBase.lean)
-/
@[path]
private lemma sixVertexFourByFourTupleGradeCountExecutable_eq_rows_eq
  {sector : Fin 5}
  {totalC : Nat} :
-- imply
  sixVertexFourByFourTupleGradeCountExecutable sector totalC = sixVertexFourByFourRowCycleGradeCountExecutable sector totalC := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourTupleGradeCountExecutable_eq_rows sector totalC

/--
[sixVertexFourByFourGradeCountExecutable_eq_rows](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourRowCycleBase.lean)
-/
@[path]
private lemma sixVertexFourByFourGradeCountExecutable_eq_rows_eq
  {sector : Fin 5}
  {totalC : Nat} :
-- imply
  sixVertexMarkedSectorRowCycleGradeCountExecutable sixVertexFourByFourTorus sector totalC = sixVertexFourByFourRowCycleGradeCountExecutable sector totalC := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourGradeCountExecutable_eq_rows sector totalC

/--
[sixVertexFourByFourVertical_last](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourRowCycleBase.lean)
-/
@[path]
private lemma sixVertexFourByFourVertical_last_eq
  {row0 row1 row2 row3 : SixVertexRow 4} :
-- imply
  (![ row0, row1, row2, row3] : Fin 4 → SixVertexRow 4) (svFinLast sixVertexFourByFourTorus.height_pos) = row3 := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourVertical_last row0 row1 row2 row3

/--
[sixVertexFourByFourWitnessProduct_certificate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourRowCycleBase.lean)
-/
@[path]
private lemma sixVertexFourByFourWitnessProduct_certificate_eq
  {index0 index1 index2 index3 : Fin 16} :
-- imply
  let vertical : Fin 4 → SixVertexRow 4 := ![ sixVertexFourRowOfIndex index0, sixVertexFourRowOfIndex index1, sixVertexFourRowOfIndex index2, sixVertexFourRowOfIndex index3] (∏ j, sixVertexHorizontalTransitionWitnessCountExecutable (T := sixVertexFourByFourTorus) vertical j) = ∏ j, sixVertexFourHorizontalTransitionCount ((![index0, index1, index2, index3] : Fin 4 → Fin 16) (SixVertexArrows.cyclicPred sixVertexFourByFourTorus.height_pos j)) ((![index0, index1, index2, index3] : Fin 4 → Fin 16) j) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourWitnessProduct_certificate index0 index1 index2 index3

/--
[sixVertexFourByFourRowCycleGradeCountExecutable_eq_cached](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourRowCycleBase.lean)
-/
@[path]
private lemma sixVertexFourByFourRowCycleGradeCountExecutable_eq_cached_eq
  {sector : Fin 5}
  {totalC : Nat} :
-- imply
  sixVertexFourByFourRowCycleGradeCountExecutable sector totalC = sixVertexFourByFourCachedGradeCount sector totalC := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourRowCycleGradeCountExecutable_eq_cached sector totalC

/--
[sixVertexFourByFourGradeCountExecutable_eq_cached](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourRowCycleBase.lean)
-/
@[path]
private lemma sixVertexFourByFourGradeCountExecutable_eq_cached_eq
  {sector : Fin 5}
  {totalC : Nat} :
-- imply
  sixVertexMarkedSectorRowCycleGradeCountExecutable sixVertexFourByFourTorus sector totalC = sixVertexFourByFourCachedGradeCount sector totalC := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByFourGradeCountExecutable_eq_cached sector totalC

/--
[sixVertexHorizontalTransitionWitnessCountExecutable_eq_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourRowCycleBase.lean)
-/
@[path]
private lemma sixVertexHorizontalTransitionWitnessCountExecutable_eq_card_eq
  {T : EvenTorus}
  {vertical : Fin T.height → SixVertexRow T.width}
  {j : Fin T.height} :
-- imply
  sixVertexHorizontalTransitionWitnessCountExecutable vertical j = Nat.card (SixVertexHorizontalTransitionWitness vertical j) := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalTransitionWitnessCountExecutable_eq_card vertical j

/--
[sixVertexMarkedSectorRowCycleGradeCountExecutable_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourRowCycleBase.lean)
-/
@[path]
private lemma sixVertexMarkedSectorRowCycleGradeCountExecutable_eq_eq
  {T : EvenTorus}
  {sector : Fin (T.width + 1)}
  {totalC : Nat} :
-- imply
  sixVertexMarkedSectorRowCycleGradeCountExecutable T sector totalC = sixVertexMarkedSectorRowCycleGradeCount T sector totalC := by
-- proof
  apply StatMech.FrontierD.sixVertexMarkedSectorRowCycleGradeCountExecutable_eq T sector totalC


-- created on 2026-10-23
