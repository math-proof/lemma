import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FiniteCumulativeGradeHall
open Finset StatMech StatMech.FrontierD


/--
[finiteGradeHall_of_upperCumulative](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteCumulativeGradeHall.lean)
-/
@[path]
private lemma finiteGradeHall_of_upperCumulative_eq
  [Fintype Source]
  [Fintype Target]
-- given
  (sourceGrade : Source -> Nat)
  (targetGrade : Target -> Nat)
  (hcumulative : forall grade, (Finset.univ.filter fun source => grade <= sourceGrade source).card <= (Finset.univ.filter fun target => grade <= targetGrade target).card) :
-- imply
  forall sources : Finset Source, sources.card <= (Finset.univ.filter fun target => ∃ source ∈ sources, sourceGrade source <= targetGrade target).card := by
-- proof
  apply StatMech.FrontierD.finiteGradeHall_of_upperCumulative sourceGrade targetGrade hcumulative

/--
[exists_injective_gradeMonotone_of_upperCumulative](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteCumulativeGradeHall.lean)
-/
@[path]
private lemma exists_injective_gradeMonotone_of_upperCumulative_eq
  [Fintype Source]
  [Fintype Target]
-- given
  (sourceGrade : Source -> Nat)
  (targetGrade : Target -> Nat)
  (hcumulative : forall grade, (Finset.univ.filter fun source => grade <= sourceGrade source).card <= (Finset.univ.filter fun target => grade <= targetGrade target).card) :
-- imply
  exists matching : Source -> Target, Function.Injective matching /\ forall source, sourceGrade source <= targetGrade (matching source) := by
-- proof
  apply StatMech.FrontierD.exists_injective_gradeMonotone_of_upperCumulative sourceGrade targetGrade hcumulative

/--
[sixVertexMarkedTraceCoefficientwiseLogConcave_of_totalCCumulative](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteCumulativeGradeHall.lean)
-/
@[path]
private lemma sixVertexMarkedTraceCoefficientwiseLogConcave_of_totalCCumulative_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hcumulative : forall totalC, (Finset.univ.filter fun pair : SixVertexMarkedSectorConfiguration T ⟨middle.val - 1, by omega⟩ × SixVertexMarkedSectorConfiguration T ⟨middle.val + 1, by omega⟩ => totalC <= sixVertexTorusCTypeCount pair.1.1 + sixVertexTorusCTypeCount pair.2.1).card <= (Finset.univ.filter fun pair : SixVertexMarkedSectorConfiguration T middle × SixVertexMarkedSectorConfiguration T middle => totalC <= sixVertexTorusCTypeCount pair.1.1 + sixVertexTorusCTypeCount pair.2.1).card) :
-- imply
  SixVertexMarkedTraceCoefficientwiseLogConcave T.width T.height middle.val := by
-- proof
  apply StatMech.FrontierD.sixVertexMarkedTraceCoefficientwiseLogConcave_of_totalCCumulative T middle hmiddle_pos hmiddle_lt hcumulative


-- created on 2026-10-23
