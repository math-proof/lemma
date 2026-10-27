import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Onsager.WalkCellLocal
open StatMech StatMech.Onsager StatMech.Onsager.WalkCellLocal


/--
[sharedPrimalEdge_mem_of_membership_diff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WalkCellLocal.lean)
-/
@[path]
private lemma sharedPrimalEdge_mem_of_membership_diff_eq
  {m : ℕ}
  {d : Fin (m + 3) → Fin 4}
  {p q : ℤ × ℤ}
-- given
  (hlat : (hypercubicLattice 2).Adj (cellFace p) (cellFace q))
  (hdiff : (p ∈ S ∧ q ∉ S) ∨ (q ∈ S ∧ p ∉ S)) :
-- imply
  sharedPrimalEdge (cellFace p) (cellFace q) ∈ (imageGraph P).edgeSet := by
-- proof
  apply StatMech.Onsager.WalkCellLocal.sharedPrimalEdge_mem_of_membership_diff d p q hlat hdiff

/--
[pinch_four_edges_impossible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WalkCellLocal.lean)
-/
@[path]
private lemma pinch_four_edges_impossible_eq
  {m : ℕ}
  {d : Fin (m + 3) → Fin 4}
  {x y : ℤ}
-- given
  (hU : sharedPrimalEdge (cellFace (x, y)) (cellFace (x - 1, y)) ∈ (imageGraph P).edgeSet)
  (hR : sharedPrimalEdge (cellFace (x, y)) (cellFace (x, y - 1)) ∈ (imageGraph P).edgeSet)
  (hL : sharedPrimalEdge (cellFace (x - 1, y)) (cellFace (x - 1, y - 1)) ∈ (imageGraph P).edgeSet) :
-- imply
  False := by
-- proof
  apply StatMech.Onsager.WalkCellLocal.pinch_four_edges_impossible d x y hU hR hL

/--
[not_pinchAt_interiorCells](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WalkCellLocal.lean)
-/
@[path]
private lemma not_pinchAt_interiorCells_eq
  {m : ℕ}
  {d : Fin (m + 3) → Fin 4}
  {v : ℤ × ℤ} :
-- imply
  ¬ pinchAt S v := by
-- proof
  apply StatMech.Onsager.WalkCellLocal.not_pinchAt_interiorCells d v

/--
[pinchCount_interiorCells_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WalkCellLocal.lean)
-/
@[path]
private lemma pinchCount_interiorCells_eq_zero_eq
  {m : ℕ}
  {d : Fin (m + 3) → Fin 4} :
-- imply
  pinchCount S = 0 := by
-- proof
  apply StatMech.Onsager.WalkCellLocal.pinchCount_interiorCells_eq_zero d


-- created on 2026-10-23
