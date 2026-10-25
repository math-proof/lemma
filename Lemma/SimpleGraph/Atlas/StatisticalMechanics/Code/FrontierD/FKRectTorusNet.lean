import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusNet.Part3
open SimpleGraph StatMech StatMech.FrontierD


/--
[fkRectCrossesHorizontalSeam_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusNet.lean)
-/
@[path]
private lemma fkRectCrossesHorizontalSeam_mk_eq
  {R : FKRectTorus}
  {x y : R.Vertex} :
-- imply
  fkRectCrossesHorizontalSeam R s(x, y) ↔ (x.1.val = 0 ∧ y.1.val + 1 = R.width) ∨ (y.1.val = 0 ∧ x.1.val + 1 = R.width) := by
-- proof
  apply StatMech.FrontierD.fkRectCrossesHorizontalSeam_mk R x y

/--
[fkRectCrossesVerticalSeam_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusNet.lean)
-/
@[path]
private lemma fkRectCrossesVerticalSeam_mk_eq
  {R : FKRectTorus}
  {x y : R.Vertex} :
-- imply
  fkRectCrossesVerticalSeam R s(x, y) ↔ (x.2.val = 0 ∧ y.2.val + 1 = R.height) ∨ (y.2.val = 0 ∧ x.2.val + 1 = R.height) := by
-- proof
  apply StatMech.FrontierD.fkRectCrossesVerticalSeam_mk R x y

/--
[not_FKRectWindingIndependent_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusNet.lean)
-/
@[path]
private lemma not_FKRectWindingIndependent_self_eq
  {u : Int × Int} :
-- imply
  ¬ FKRectWindingIndependent u u := by
-- proof
  apply StatMech.FrontierD.not_FKRectWindingIndependent_self u

/--
[fkRect_diagonal_winding_not_independent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusNet.lean)
-/
@[path]
private lemma fkRect_diagonal_winding_not_independent_eq :
-- imply
  ¬ FKRectWindingIndependent ((1, 1) : Int × Int) (1, 1) := by
-- proof
  apply StatMech.FrontierD.fkRect_diagonal_winding_not_independent

/--
[fkRectNetIndicator_eq_one_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusNet.lean)
-/
@[path]
private lemma fkRectNetIndicator_eq_one_iff_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  fkRectNetIndicator R omega = 1 ↔ FKRectHasNet R omega := by
-- proof
  apply StatMech.FrontierD.fkRectNetIndicator_eq_one_iff R omega

/--
[fkRectNetIndicator_eq_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusNet.lean)
-/
@[path]
private lemma fkRectNetIndicator_eq_zero_iff_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  fkRectNetIndicator R omega = 0 ↔ ¬ FKRectHasNet R omega := by
-- proof
  apply StatMech.FrontierD.fkRectNetIndicator_eq_zero_iff R omega

/--
[fkRectNetIndicator_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusNet.lean)
-/
@[path]
private lemma fkRectNetIndicator_le_one_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  fkRectNetIndicator R omega ≤ 1 := by
-- proof
  apply StatMech.FrontierD.fkRectNetIndicator_le_one R omega


-- created on 2026-10-23
