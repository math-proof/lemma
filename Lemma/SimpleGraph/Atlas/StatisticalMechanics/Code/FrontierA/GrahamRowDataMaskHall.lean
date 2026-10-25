import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamRowDataMaskHall.Part2
open Finset Classical StatMech StatMech.GrahamGHS StatMech.GrahamGHS.FourColor


/--
[rowDataRepairEmbedding_of_maskFiberEmbeddings_related](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamRowDataMaskHall.lean)
-/
@[path]
private lemma rowDataRepairEmbedding_of_maskFiberEmbeddings_related_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {f : MaskFiberEmbeddings ends m j k l zero}
  {d : leftRowData ends m j k l zero}
-- given
  (ends : I -> Sym2 W) :
-- imply
  RowDataRepairRelated ends m j k l zero d (rowDataRepairEmbedding_of_maskFiberEmbeddings ends m j k l zero f d) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.rowDataRepairEmbedding_of_maskFiberEmbeddings_related ends m j k l zero f d

/--
[rowDataRepairHall_of_maskFiberEmbeddings](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamRowDataMaskHall.lean)
-/
@[path]
private lemma rowDataRepairHall_of_maskFiberEmbeddings_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {f : MaskFiberEmbeddings ends m j k l zero}
-- given
  (ends : I -> Sym2 W) :
-- imply
  RowDataRepairHall ends m j k l zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.rowDataRepairHall_of_maskFiberEmbeddings ends m j k l zero f

/--
[rowDataRepairHall_of_maskwise](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamRowDataMaskHall.lean)
-/
@[path]
private lemma rowDataRepairHall_of_maskwise_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
-- given
  (ends : I -> Sym2 W)
  (hmask : forall p : Finset I × Finset I, Fintype.card (leftMaskFiber ends m j k l zero p) <= Fintype.card (rightMaskFiber ends m j k l zero p)) :
-- imply
  RowDataRepairHall ends m j k l zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.rowDataRepairHall_of_maskwise ends m j k l zero hmask

/--
[rowDataRepairHall_iff_maskwise](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamRowDataMaskHall.lean)
-/
@[path]
private lemma rowDataRepairHall_iff_maskwise_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
-- given
  (ends : I -> Sym2 W) :
-- imply
  RowDataRepairHall ends m j k l zero ↔ forall p : Finset I × Finset I, Fintype.card (leftMaskFiber ends m j k l zero p) <= Fintype.card (rightMaskFiber ends m j k l zero p) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.rowDataRepairHall_iff_maskwise ends m j k l zero

/--
[rowDataRepairHall_of_subsingleton_leftMaskFibers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamRowDataMaskHall.lean)
-/
@[path]
private lemma rowDataRepairHall_of_subsingleton_leftMaskFibers_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
-- given
  (ends : I -> Sym2 W)
  (hloop : forall i, i ∈ m -> ¬(ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hsub : forall p : Finset I × Finset I, Subsingleton (leftMaskFiber ends m j k l zero p)) :
-- imply
  RowDataRepairHall ends m j k l zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.rowDataRepairHall_of_subsingleton_leftMaskFibers ends m j k l zero hloop hjk hkl hk0 hsub

/--
[rowDataRepairHall_of_subsingleton_cycleSectors](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamRowDataMaskHall.lean)
-/
@[path]
private lemma rowDataRepairHall_of_subsingleton_cycleSectors_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
-- given
  (ends : I -> Sym2 W)
  (hloop : forall i, i ∈ m -> ¬(ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hcycle : forall p : Finset I × Finset I, Subsingleton (boundarySector ends p.1 ∅) ∧ Subsingleton (boundarySector ends p.2 ∅)) :
-- imply
  RowDataRepairHall ends m j k l zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.rowDataRepairHall_of_subsingleton_cycleSectors ends m j k l zero hloop hjk hkl hk0 hcycle


-- created on 2026-10-23
