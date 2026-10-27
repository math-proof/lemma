import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamRowDataRepairRelation.Part4
open Finset StatMech StatMech.GrahamGHS StatMech.GrahamGHS.FourColor


/--
[mem_admissibleRightRowRepairs_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamRowDataRepairRelation.lean)
-/
@[path]
private lemma mem_admissibleRightRowRepairs_iff_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I → Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {d : leftRowData ends m j k l zero}
  {e : rightRowData ends m j k l zero} :
-- imply
  e ∈ admissibleRightRowRepairs ends m j k l zero d ↔ RowDataRepairRelated ends m j k l zero d e := by
-- proof
  apply StatMech.GrahamGHS.FourColor.mem_admissibleRightRowRepairs_iff ends m j k l zero d e

/--
[rowDataRepairRelated_iff_sameMask](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamRowDataRepairRelation.lean)
-/
@[path]
private lemma rowDataRepairRelated_iff_sameMask_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I → Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {d : leftRowData ends m j k l zero}
  {e : rightRowData ends m j k l zero} :
-- imply
  RowDataRepairRelated ends m j k l zero d e ↔ fourColorMaskProfile m (rowDataToLeftFiber ends m j k l zero d).1 = fourColorMaskProfile m (rowDataToRightFiber ends m j k l zero e).1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.rowDataRepairRelated_iff_sameMask ends m j k l zero d e

/--
[canonicalRightRowData_mem_admissibleRightRowRepairs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamRowDataRepairRelation.lean)
-/
@[path]
private lemma canonicalRightRowData_mem_admissibleRightRowRepairs_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I → Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {d : leftRowData ends m j k l zero}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero) :
-- imply
  canonicalRightRowData ends m j k l zero hloop hjk hkl hk0 d ∈ admissibleRightRowRepairs ends m j k l zero d := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalRightRowData_mem_admissibleRightRowRepairs ends m j k l zero hloop hjk hkl hk0 d

/--
[mem_admissibleRightRowNeighborhood_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamRowDataRepairRelation.lean)
-/
@[path]
private lemma mem_admissibleRightRowNeighborhood_iff_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I → Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {S : Finset (leftRowData ends m j k l zero)}
  {e : rightRowData ends m j k l zero} :
-- imply
  e ∈ admissibleRightRowNeighborhood ends m j k l zero S ↔ ∃ d ∈ S, RowDataRepairRelated ends m j k l zero d e := by
-- proof
  apply StatMech.GrahamGHS.FourColor.mem_admissibleRightRowNeighborhood_iff ends m j k l zero S e

/--
[rowDataRepairHall_of_related_embedding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamRowDataRepairRelation.lean)
-/
@[path]
private lemma rowDataRepairHall_of_related_embedding_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I → Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {f : leftRowData ends m j k l zero ↪ rightRowData ends m j k l zero}
-- given
  (hrelated : ∀ d, RowDataRepairRelated ends m j k l zero d (f d)) :
-- imply
  RowDataRepairHall ends m j k l zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.rowDataRepairHall_of_related_embedding ends m j k l zero f hrelated

/--
[GrahamWeightedRowMinor_of_rowDataRepairHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamRowDataRepairRelation.lean)
-/
@[path]
private lemma GrahamWeightedRowMinor_of_rowDataRepairHall_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I → Sym2 W}
  {m : Finset I}
  {j k l zero : W}
-- given
  (hhall : RowDataRepairHall ends m j k l zero) :
-- imply
  GrahamWeightedRowMinor ends m j k l zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.GrahamWeightedRowMinor_of_rowDataRepairHall ends m j k l zero hhall


-- created on 2026-10-23
