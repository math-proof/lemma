import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Onsager.CellEulerFaithful.Part6
open StatMech StatMech.Onsager StatMech.Onsager.CellEulerFaithful


/--
[regEdge_mem_imageGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellEulerFaithful.lean)
-/
@[path]
private lemma regEdge_mem_imageGraph_eq
  {S : Finset Cell}
  {e : Sym2 Vtx}
-- given
  (he : e ∈ StatMech.Euc.regEdges S) :
-- imply
  Sym2.map (fun v : Vtx => ![v.1, v.2]) e ∈ (imageGraph (cellSkeletonP S)).edgeSet := by
-- proof
  apply StatMech.Onsager.CellEulerFaithful.regEdge_mem_imageGraph S he

/--
[sharedPrimalEdge_mem_regEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellEulerFaithful.lean)
-/
@[path]
private lemma sharedPrimalEdge_mem_regEdges_eq
  {S : Finset Cell}
  {c : Cell}
  {g : Site 2}
-- given
  (hc : c ∈ S)
  (hlat : (hypercubicLattice 2).Adj (cellFace c) g) :
-- imply
  Sym2.map cellFace.symm (sharedPrimalEdge (cellFace c) g) ∈ StatMech.Euc.regEdges S := by
-- proof
  apply StatMech.Onsager.CellEulerFaithful.sharedPrimalEdge_mem_regEdges S c hc g hlat

/--
[occupiedFace_isolated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellEulerFaithful.lean)
-/
@[path]
private lemma occupiedFace_isolated_eq
  {S : Finset Cell}
  {c : Cell}
  {g : Site 2}
-- given
  (hc : c ∈ S) :
-- imply
  ¬ (whb_faceRegion (imageGraph (cellSkeletonP S))).Adj (cellFace c) g := by
-- proof
  apply StatMech.Onsager.CellEulerFaithful.occupiedFace_isolated S c hc g

/--
[occupiedFace_reachable_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellEulerFaithful.lean)
-/
@[path]
private lemma occupiedFace_reachable_eq_eq
  {S : Finset Cell}
  {c : Cell}
  {g : Site 2}
-- given
  (hc : c ∈ S)
  (hreach : (whb_faceRegion (imageGraph (cellSkeletonP S))).Reachable (cellFace c) g) :
-- imply
  g = cellFace c := by
-- proof
  apply StatMech.Onsager.CellEulerFaithful.occupiedFace_reachable_eq S c hc g hreach

/--
[occupiedComponent_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellEulerFaithful.lean)
-/
@[path]
private lemma occupiedComponent_finite_eq
  {S : Finset Cell}
  {c : Cell}
-- given
  (hc : c ∈ S) :
-- imply
  (occupiedComponent S c).supp.Finite := by
-- proof
  apply StatMech.Onsager.CellEulerFaithful.occupiedComponent_finite S c hc

/--
[occupiedBoundedFace_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellEulerFaithful.lean)
-/
@[path]
private lemma occupiedBoundedFace_injective_eq
  {S : Finset Cell} :
-- imply
  Function.Injective (occupiedBoundedFace S) := by
-- proof
  apply StatMech.Onsager.CellEulerFaithful.occupiedBoundedFace_injective S

/--
[card_le_cellSkeleton_nullity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellEulerFaithful.lean)
-/
@[path]
private lemma card_le_cellSkeleton_nullity_eq
  {S : Finset Cell} :
-- imply
  S.card ≤ nullity (cellSkeletonP S).G := by
-- proof
  apply StatMech.Onsager.CellEulerFaithful.card_le_cellSkeleton_nullity S

/--
[mem_cellSkeleton_edgeSet_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellEulerFaithful.lean)
-/
@[path]
private lemma mem_cellSkeleton_edgeSet_iff_eq
  {S : Finset Cell}
-- given
  (e : Sym2 {v // v ∈ regVerts S}) :
-- imply
  e ∈ (cellSkeleton S).edgeSet ↔ Sym2.map Subtype.val e ∈ StatMech.Euc.regEdges S := by
-- proof
  apply StatMech.Onsager.CellEulerFaithful.mem_cellSkeleton_edgeSet_iff S e

/--
[card_cellSkeleton_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellEulerFaithful.lean)
-/
@[path]
private lemma card_cellSkeleton_edges_eq
  {S : Finset Cell} :
-- imply
  Nat.card (cellSkeleton S).edgeSet = (StatMech.Euc.regEdges S).card := by
-- proof
  apply StatMech.Onsager.CellEulerFaithful.card_cellSkeleton_edges S

/--
[card_cellSkeleton_vertices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellEulerFaithful.lean)
-/
@[path]
private lemma card_cellSkeleton_vertices_eq
  {S : Finset Cell} :
-- imply
  Nat.card {v // v ∈ regVerts S} = (regVerts S).card := by
-- proof
  apply StatMech.Onsager.CellEulerFaithful.card_cellSkeleton_vertices S

/--
[eulerChar_le_one_of_skeleton_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellEulerFaithful.lean)
-/
@[path]
private lemma eulerChar_le_one_of_skeleton_connected_eq
  {S : Finset Cell}
-- given
  (hconn : (cellSkeleton S).Connected) :
-- imply
  eulerChar S ≤ 1 := by
-- proof
  apply StatMech.Onsager.CellEulerFaithful.eulerChar_le_one_of_skeleton_connected S hconn

/--
[corner_reachable_lowerLeft](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellEulerFaithful.lean)
-/
@[path]
private lemma corner_reachable_lowerLeft_eq
  {S : Finset Cell}
  {c : Cell}
  {v : Vtx}
-- given
  (hc : c ∈ S)
  (hv : v ∈ StatMech.Euc.cellVerts c) :
-- imply
  (cellSkeleton S).Reachable (skeletonVertexOfCorner S c hc v hv) (skeletonVertexOfCorner S c hc c (by obtain ⟨x, y⟩ := c simp [StatMech.Euc.cellVerts])) := by
-- proof
  apply StatMech.Onsager.CellEulerFaithful.corner_reachable_lowerLeft S c hc v hv

/--
[cell_representatives_reachable_of_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellEulerFaithful.lean)
-/
@[path]
private lemma cell_representatives_reachable_of_adj_eq
  {S : Finset Cell}
  {c d : Cell}
-- given
  (hc : c ∈ S)
  (hd : d ∈ S)
  (hadj : (hypercubicLattice 2).Adj (cellFace c) (cellFace d)) :
-- imply
  (cellSkeleton S).Reachable (skeletonVertexOfCorner S c hc c (by obtain ⟨x, y⟩ := c; simp [StatMech.Euc.cellVerts])) (skeletonVertexOfCorner S d hd d (by obtain ⟨x, y⟩ := d; simp [StatMech.Euc.cellVerts])) := by let e := Sym2.map cellFace.symm (sharedPrimalEdge (cellFace c) (cellFace d)) have hec : e ∈ StatMech.Euc.regEdges ({c} : Finset Cell) := sharedPrimalEdge_mem_regEdges {c} c (by simp) (cellFace d) hadj have hed : e ∈ StatMech.Euc.regEdges ({d} : Finset Cell) := by have h := sharedPrimalEdge_mem_regEdges {d} d (by simp) (cellFace c) hadj.symm rw [← sharedPrimalEdge_comm_of_adj hadj] at h exact h generalize heq : e = edge at hec hed induction edge with := by
-- proof
  apply StatMech.Onsager.CellEulerFaithful.cell_representatives_reachable_of_adj S c d hc hd hadj

/--
[interior_representatives_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellEulerFaithful.lean)
-/
@[path]
private lemma interior_representatives_reachable_eq
  {m : ℕ}
  {d : Fin (m + 3) → Fin 4}
  {c e : interiorCells d hclosed hsimple hreflexfree}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (BaseCase.pos d))
  (hreflexfree : ∀ i : Fin (m + 3), d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) :
-- imply
  (cellSkeleton (interiorCells d hclosed hsimple hreflexfree)).Reachable (skeletonRepresentative _ c) (skeletonRepresentative _ e) := by
-- proof
  apply StatMech.Onsager.CellEulerFaithful.interior_representatives_reachable d hclosed hsimple hreflexfree c e

/--
[interior_cellSkeleton_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellEulerFaithful.lean)
-/
@[path]
private lemma interior_cellSkeleton_connected_eq
  {m : ℕ}
  {d : Fin (m + 3) → Fin 4}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (hreflexfree : ∀ i : Fin (m + 3), d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) :
-- imply
  (cellSkeleton (interiorCells d hclosed hsimple hreflexfree)).Connected := by
-- proof
  apply StatMech.Onsager.CellEulerFaithful.interior_cellSkeleton_connected d hclosed hsimple hreflexfree

/--
[eulerChar_interiorCells_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellEulerFaithful.lean)
-/
@[path]
private lemma eulerChar_interiorCells_le_one_eq
  {m : ℕ}
  {d : Fin (m + 3) → Fin 4}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (hreflexfree : ∀ i : Fin (m + 3), d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) :
-- imply
  eulerChar (interiorCells d hclosed hsimple hreflexfree) ≤ 1 := by
-- proof
  apply StatMech.Onsager.CellEulerFaithful.eulerChar_interiorCells_le_one d hclosed hsimple hreflexfree


-- created on 2026-10-23
