import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Onsager.CellConnect2
open StatMech StatMech.Onsager StatMech.Onsager.CellConnect2


/--
[cornerWeight_eq_icw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellConnect2.lean)
-/
@[path]
private lemma cornerWeight_eq_icw_eq
  {m : ℕ} :
-- imply
  cornerWeight m = icw (m : ℤ) := by
-- proof
  apply StatMech.Onsager.CellConnect2.cornerWeight_eq_icw m

/--
[cornerWeight_jump](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellConnect2.lean)
-/
@[path]
private lemma cornerWeight_jump_eq
  {m : ℕ} :
-- imply
  cornerWeight (m + 1) - cornerWeight m = ijump (m : ℤ) := by
-- proof
  apply StatMech.Onsager.CellConnect2.cornerWeight_jump m

/--
[bI_decide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellConnect2.lean)
-/
@[path]
private lemma bI_decide_eq
  [Decidable p]
-- given
  (p : Prop) :
-- imply
  bI (decide p) = if p then 1 else 0 := by
-- proof
  apply StatMech.Onsager.CellConnect2.bI_decide p

/--
[cornerDiff_jump_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellConnect2.lean)
-/
@[path]
private lemma cornerDiff_jump_sum_eq
  {S : Finset (ℤ × ℤ)}
  {x y : ℤ}
-- given
  (hc : (x, y) ∉ S) :
-- imply
  (∑ v ∈ cornersOf (x, y), (cornerWeight (cornerCount S v + 1) - cornerWeight (cornerCount S v))) = lhsLocal (decide ((x + 1, y) ∈ S)) (decide ((x - 1, y) ∈ S)) (decide ((x, y + 1) ∈ S)) (decide ((x, y - 1) ∈ S)) (decide ((x + 1, y + 1) ∈ S)) (decide ((x - 1, y + 1) ∈ S)) (decide ((x + 1, y - 1) ∈ S)) (decide ((x - 1, y - 1) ∈ S)) := by
-- proof
  apply StatMech.Onsager.CellConnect2.cornerDiff_jump_sum S x y hc

/--
[notMem_cellVerts_iff_cornerCount_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellConnect2.lean)
-/
@[path]
private lemma notMem_cellVerts_iff_cornerCount_zero_eq
  {S : Finset (ℤ × ℤ)}
  {v : ℤ × ℤ} :
-- imply
  v ∉ cellVerts S ↔ cornerCount S v = 0 := by
-- proof
  apply StatMech.Onsager.CellConnect2.notMem_cellVerts_iff_cornerCount_zero S v

/--
[card_sdiff_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellConnect2.lean)
-/
@[path]
private lemma card_sdiff_eq_sum_eq
  {s t : Finset (ℤ × ℤ)} :
-- imply
  ((s \ t).card : ℤ) = ∑ v ∈ s, (if v ∉ t then (1 : ℤ) else 0) := by
-- proof
  apply StatMech.Onsager.CellConnect2.card_sdiff_eq_sum s t

/--
[sdiff_cellVerts_card_eq_deltaV](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellConnect2.lean)
-/
@[path]
private lemma sdiff_cellVerts_card_eq_deltaV_eq
  {S : Finset (ℤ × ℤ)}
  {x y : ℤ}
-- given
  (hc : (x, y) ∉ S) :
-- imply
  ((cornersOf (x, y) \ cellVerts S).card : ℤ) = deltaV (decide ((x + 1, y) ∈ S)) (decide ((x - 1, y) ∈ S)) (decide ((x, y + 1) ∈ S)) (decide ((x, y - 1) ∈ S)) (decide ((x + 1, y + 1) ∈ S)) (decide ((x - 1, y + 1) ∈ S)) (decide ((x + 1, y - 1) ∈ S)) (decide ((x - 1, y - 1) ∈ S)) := by
-- proof
  apply StatMech.Onsager.CellConnect2.sdiff_cellVerts_card_eq_deltaV S x y hc

/--
[mem_cellEdges_bottom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellConnect2.lean)
-/
@[path]
private lemma mem_cellEdges_bottom_eq
  {S : Finset (ℤ × ℤ)}
  {x y : ℤ} :
-- imply
  ((2 * x + 1, 2 * y) : ℤ × ℤ) ∈ cellEdges S ↔ (x, y) ∈ S ∨ (x, y - 1) ∈ S := by
-- proof
  apply StatMech.Onsager.CellConnect2.mem_cellEdges_bottom S x y

/--
[mem_cellEdges_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellConnect2.lean)
-/
@[path]
private lemma mem_cellEdges_top_eq
  {S : Finset (ℤ × ℤ)}
  {x y : ℤ} :
-- imply
  ((2 * x + 1, 2 * y + 2) : ℤ × ℤ) ∈ cellEdges S ↔ (x, y) ∈ S ∨ (x, y + 1) ∈ S := by
-- proof
  apply StatMech.Onsager.CellConnect2.mem_cellEdges_top S x y

/--
[mem_cellEdges_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellConnect2.lean)
-/
@[path]
private lemma mem_cellEdges_left_eq
  {S : Finset (ℤ × ℤ)}
  {x y : ℤ} :
-- imply
  ((2 * x, 2 * y + 1) : ℤ × ℤ) ∈ cellEdges S ↔ (x, y) ∈ S ∨ (x - 1, y) ∈ S := by
-- proof
  apply StatMech.Onsager.CellConnect2.mem_cellEdges_left S x y

/--
[mem_cellEdges_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellConnect2.lean)
-/
@[path]
private lemma mem_cellEdges_right_eq
  {S : Finset (ℤ × ℤ)}
  {x y : ℤ} :
-- imply
  ((2 * x + 2, 2 * y + 1) : ℤ × ℤ) ∈ cellEdges S ↔ (x, y) ∈ S ∨ (x + 1, y) ∈ S := by
-- proof
  apply StatMech.Onsager.CellConnect2.mem_cellEdges_right S x y

/--
[sdiff_cellEdges_card_eq_deltaE](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellConnect2.lean)
-/
@[path]
private lemma sdiff_cellEdges_card_eq_deltaE_eq
  {S : Finset (ℤ × ℤ)}
  {x y : ℤ}
-- given
  (hc : (x, y) ∉ S) :
-- imply
  ((edgesOf (x, y) \ cellEdges S).card : ℤ) = deltaE (decide ((x + 1, y) ∈ S)) (decide ((x - 1, y) ∈ S)) (decide ((x, y + 1) ∈ S)) (decide ((x, y - 1) ∈ S)) := by
-- proof
  apply StatMech.Onsager.CellConnect2.sdiff_cellEdges_card_eq_deltaE S x y hc


-- created on 2026-10-23
