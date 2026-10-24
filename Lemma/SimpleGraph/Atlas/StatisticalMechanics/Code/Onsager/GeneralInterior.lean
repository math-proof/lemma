import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Onsager.GeneralInterior
open StatMech StatMech.Onsager StatMech.Onsager.GeneralInterior


/--
[exists_odd_cell_at_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/GeneralInterior.lean)
-/
@[path]
private lemma exists_odd_cell_at_edge_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {k : Fin n}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (hn : 3 ≤ n) :
-- imply
  ∃ c : ℤ × ℤ, rayParity d c.1 c.2 = 1 := by
-- proof
  apply StatMech.Onsager.GeneralInterior.exists_odd_cell_at_edge d hclosed hsimple hn k

/--
[interiorCells_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/GeneralInterior.lean)
-/
@[path]
private lemma interiorCells_nonempty_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (hn : 3 ≤ n) :
-- imply
  (interiorCells d hclosed).Nonempty := by
-- proof
  apply StatMech.Onsager.GeneralInterior.interiorCells_nonempty d hclosed hsimple hn

/--
[oddComponent_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/GeneralInterior.lean)
-/
@[path]
private lemma oddComponent_finite_eq
  {n : ℕ}
  [NeZero n]
  {m : ℕ}
  {d : Fin (m + 3) → Fin 4}
  {c : interiorCells d hclosed}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d)) :
-- imply
  (oddComponent d hclosed hsimple c).supp.Finite := by
-- proof
  apply StatMech.Onsager.GeneralInterior.oddComponent_finite d hclosed hsimple c

/--
[odd_cells_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/GeneralInterior.lean)
-/
@[path]
private lemma odd_cells_reachable_eq
  {n : ℕ}
  [NeZero n]
  {m : ℕ}
  {d : Fin (m + 3) → Fin 4}
  {c e : interiorCells d hclosed}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d)) :
-- imply
  (walkRegionGraph d hclosed hsimple).Reachable (cellFace c.1) (cellFace e.1) := by
-- proof
  apply StatMech.Onsager.GeneralInterior.odd_cells_reachable d hclosed hsimple c e

/--
[even_cell_reaches_beacon](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/GeneralInterior.lean)
-/
@[path]
private lemma even_cell_reaches_beacon_eq
  {n : ℕ}
  [NeZero n]
  {m : ℕ}
  {d : Fin (m + 3) → Fin 4}
  {p : ℤ × ℤ}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (hp : rayParity d p.1 p.2 = 0) :
-- imply
  (walkRegionGraph d hclosed hsimple).Reachable (cellFace p) (beacon 2 (outerBoxRadius (walkP d hclosed hsimple) + 1)) := by
-- proof
  apply StatMech.Onsager.GeneralInterior.even_cell_reaches_beacon d hclosed hsimple p hp

/--
[outside_cell_reaches_beacon](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/GeneralInterior.lean)
-/
@[path]
private lemma outside_cell_reaches_beacon_eq
  {n : ℕ}
  [NeZero n]
  {m : ℕ}
  {d : Fin (m + 3) → Fin 4}
  {p : ℤ × ℤ}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (hp : p ∉ InteriorCells.interiorCells d hclosed) :
-- imply
  (walkRegionGraph d hclosed hsimple).Reachable (cellFace p) (beacon 2 (outerBoxRadius (walkP d hclosed hsimple) + 1)) := by
-- proof
  apply StatMech.Onsager.GeneralInterior.outside_cell_reaches_beacon d hclosed hsimple p hp

/--
[vertical_sharedEdge_mem_regEdges_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/GeneralInterior.lean)
-/
@[path]
private lemma vertical_sharedEdge_mem_regEdges_iff_eq
  {n : ℕ}
  [NeZero n]
  {m : ℕ}
  {S : Finset (ℤ × ℤ)}
  {x y : ℤ} :
-- imply
  Sym2.map cellFace.symm (sharedPrimalEdge (cellFace (x, y)) (cellFace (x + 1, y))) ∈ StatMech.Euc.regEdges S ↔ (x, y) ∈ S ∨ (x + 1, y) ∈ S := by
-- proof
  apply StatMech.Onsager.GeneralInterior.vertical_sharedEdge_mem_regEdges_iff S x y

/--
[horizontal_sharedEdge_mem_regEdges_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/GeneralInterior.lean)
-/
@[path]
private lemma horizontal_sharedEdge_mem_regEdges_iff_eq
  {n : ℕ}
  [NeZero n]
  {m : ℕ}
  {S : Finset (ℤ × ℤ)}
  {x y : ℤ} :
-- imply
  Sym2.map cellFace.symm (sharedPrimalEdge (cellFace (x, y)) (cellFace (x, y + 1))) ∈ StatMech.Euc.regEdges S ↔ (x, y) ∈ S ∨ (x, y + 1) ∈ S := by
-- proof
  apply StatMech.Onsager.GeneralInterior.horizontal_sharedEdge_mem_regEdges_iff S x y

/--
[sharedEdge_mem_regEdges_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/GeneralInterior.lean)
-/
@[path]
private lemma sharedEdge_mem_regEdges_iff_eq
  {n : ℕ}
  [NeZero n]
  {m : ℕ}
  {S : Finset (ℤ × ℤ)}
  {p q : ℤ × ℤ}
-- given
  (hlat : (hypercubicLattice 2).Adj (cellFace p) (cellFace q)) :
-- imply
  Sym2.map cellFace.symm (sharedPrimalEdge (cellFace p) (cellFace q)) ∈ StatMech.Euc.regEdges S ↔ p ∈ S ∨ q ∈ S := by
-- proof
  apply StatMech.Onsager.GeneralInterior.sharedEdge_mem_regEdges_iff S p q hlat

/--
[regEdge_of_mem_cellSkeleton_image](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/GeneralInterior.lean)
-/
@[path]
private lemma regEdge_of_mem_cellSkeleton_image_eq
  {n : ℕ}
  [NeZero n]
  {m : ℕ}
  {S : Finset (ℤ × ℤ)}
  {e : Sym2 (Site 2)}
-- given
  (he : e ∈ (imageGraph (cellSkeletonP S)).edgeSet) :
-- imply
  Sym2.map cellFace.symm e ∈ StatMech.Euc.regEdges S := by
-- proof
  apply StatMech.Onsager.GeneralInterior.regEdge_of_mem_cellSkeleton_image S e he

/--
[outside_faceAdj_cellSkeleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/GeneralInterior.lean)
-/
@[path]
private lemma outside_faceAdj_cellSkeleton_eq
  {n : ℕ}
  [NeZero n]
  {m : ℕ}
  {S : Finset (ℤ × ℤ)}
  {p q : ℤ × ℤ}
-- given
  (hp : p ∉ S)
  (hq : q ∉ S)
  (hlat : (hypercubicLattice 2).Adj (cellFace p) (cellFace q)) :
-- imply
  (whb_faceRegion (imageGraph (cellSkeletonP S))).Adj (cellFace p) (cellFace q) := by
-- proof
  apply StatMech.Onsager.GeneralInterior.outside_faceAdj_cellSkeleton S p q hp hq hlat

/--
[outside_cell_reaches_beacon_cellSkeleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/GeneralInterior.lean)
-/
@[path]
private lemma outside_cell_reaches_beacon_cellSkeleton_eq
  {n : ℕ}
  [NeZero n]
  {m : ℕ}
  {d : Fin (m + 3) → Fin 4}
  {p : ℤ × ℤ}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (hp : p ∉ InteriorCells.interiorCells d hclosed) :
-- imply
  (whb_faceRegion (imageGraph (cellSkeletonP (InteriorCells.interiorCells d hclosed)))).Reachable (cellFace p) (beacon 2 (outerBoxRadius (walkP d hclosed hsimple) + 1)) := by
-- proof
  apply StatMech.Onsager.GeneralInterior.outside_cell_reaches_beacon_cellSkeleton d hclosed hsimple p hp

/--
[outside_cell_component_eq_outer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/GeneralInterior.lean)
-/
@[path]
private lemma outside_cell_component_eq_outer_eq
  {n : ℕ}
  [NeZero n]
  {m : ℕ}
  {d : Fin (m + 3) → Fin 4}
  {p : ℤ × ℤ}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (hp : p ∉ InteriorCells.interiorCells d hclosed) :
-- imply
  (whb_faceRegion (imageGraph (cellSkeletonP (InteriorCells.interiorCells d hclosed)))).connectedComponentMk (cellFace p) = jfc_whb_outerRegion (cellSkeletonP (InteriorCells.interiorCells d hclosed)) := by
-- proof
  apply StatMech.Onsager.GeneralInterior.outside_cell_component_eq_outer d hclosed hsimple p hp

/--
[occupiedBoundedFace_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/GeneralInterior.lean)
-/
@[path]
private lemma occupiedBoundedFace_surjective_eq
  {n : ℕ}
  [NeZero n]
  {m : ℕ}
  {d : Fin (m + 3) → Fin 4}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d)) :
-- imply
  Function.Surjective (occupiedBoundedFace (InteriorCells.interiorCells d hclosed)) := by
-- proof
  apply StatMech.Onsager.GeneralInterior.occupiedBoundedFace_surjective d hclosed hsimple

/--
[cellSkeleton_nullity_eq_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/GeneralInterior.lean)
-/
@[path]
private lemma cellSkeleton_nullity_eq_card_eq
  {n : ℕ}
  [NeZero n]
  {m : ℕ}
  {d : Fin (m + 3) → Fin 4}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d)) :
-- imply
  nullity (cellSkeleton (InteriorCells.interiorCells d hclosed)) = (InteriorCells.interiorCells d hclosed).card := by
-- proof
  apply StatMech.Onsager.GeneralInterior.cellSkeleton_nullity_eq_card d hclosed hsimple

/--
[interior_cellSkeleton_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/GeneralInterior.lean)
-/
@[path]
private lemma interior_cellSkeleton_connected_eq
  {n : ℕ}
  [NeZero n]
  {m : ℕ}
  {d : Fin (m + 3) → Fin 4}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d)) :
-- imply
  (cellSkeleton (InteriorCells.interiorCells d hclosed)).Connected := by
-- proof
  apply StatMech.Onsager.GeneralInterior.interior_cellSkeleton_connected d hclosed hsimple

/--
[eulerChar_interiorCells_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/GeneralInterior.lean)
-/
@[path]
private lemma eulerChar_interiorCells_le_one_eq
  {n : ℕ}
  [NeZero n]
  {m : ℕ}
  {d : Fin (m + 3) → Fin 4}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d)) :
-- imply
  eulerChar (InteriorCells.interiorCells d hclosed) ≤ 1 := by
-- proof
  apply StatMech.Onsager.GeneralInterior.eulerChar_interiorCells_le_one d hclosed hsimple

/--
[eulerChar_interiorCells_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/GeneralInterior.lean)
-/
@[path]
private lemma eulerChar_interiorCells_eq_one_eq
  {n : ℕ}
  [NeZero n]
  {m : ℕ}
  {d : Fin (m + 3) → Fin 4}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d)) :
-- imply
  eulerChar (InteriorCells.interiorCells d hclosed) = 1 := by
-- proof
  apply StatMech.Onsager.GeneralInterior.eulerChar_interiorCells_eq_one d hclosed hsimple


-- created on 2026-10-23
