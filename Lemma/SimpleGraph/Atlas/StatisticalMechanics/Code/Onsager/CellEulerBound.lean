import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Onsager.CellEulerBound.Part4
open StatMech StatMech.Onsager StatMech.Onsager.CellEulerBound


/--
[edgeCode_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellEulerBound.lean)
-/
@[path]
private lemma edgeCode_mk_eq
  {a b : ℤ × ℤ} :
-- imply
  edgeCode s(a, b) = (a.1 + b.1, a.2 + b.2) := by
-- proof
  apply StatMech.Onsager.CellEulerBound.edgeCode_mk a b

/--
[image_cellEdges_edgeCode](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellEulerBound.lean)
-/
@[path]
private lemma image_cellEdges_edgeCode_eq
  {c : Cell} :
-- imply
  (StatMech.Euc.cellEdges c).image edgeCode = edgesOf c := by
-- proof
  apply StatMech.Onsager.CellEulerBound.image_cellEdges_edgeCode c

/--
[image_regEdges_edgeCode](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellEulerBound.lean)
-/
@[path]
private lemma image_regEdges_edgeCode_eq
  {S : Finset Cell} :
-- imply
  (regEdges S).image edgeCode = StatMech.Onsager.CellEuler.cellEdges S := by
-- proof
  apply StatMech.Onsager.CellEulerBound.image_regEdges_edgeCode S

/--
[edgeCode_injOn_regEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellEulerBound.lean)
-/
@[path]
private lemma edgeCode_injOn_regEdges_eq
  {S : Finset Cell} :
-- imply
  Set.InjOn edgeCode (regEdges S) := by
-- proof
  apply StatMech.Onsager.CellEulerBound.edgeCode_injOn_regEdges S

/--
[card_cellEdges_eq_regEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellEulerBound.lean)
-/
@[path]
private lemma card_cellEdges_eq_regEdges_eq
  {S : Finset Cell} :
-- imply
  (StatMech.Onsager.CellEuler.cellEdges S).card = (regEdges S).card := by
-- proof
  apply StatMech.Onsager.CellEulerBound.card_cellEdges_eq_regEdges S

/--
[cellVerts_eq_regVerts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellEulerBound.lean)
-/
@[path]
private lemma cellVerts_eq_regVerts_eq
  {S : Finset Cell} :
-- imply
  StatMech.Onsager.CellCount.cellVerts S = regVerts S := by
-- proof
  apply StatMech.Onsager.CellEulerBound.cellVerts_eq_regVerts S

/--
[eulerChar_eq_regChi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellEulerBound.lean)
-/
@[path]
private lemma eulerChar_eq_regChi_eq
  {S : Finset Cell} :
-- imply
  eulerChar S = regChi S := by
-- proof
  apply StatMech.Onsager.CellEulerBound.eulerChar_eq_regChi S

/--
[topEdge_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellEulerBound.lean)
-/
@[path]
private lemma topEdge_injective_eq :
-- imply
  Function.Injective topEdge := by
-- proof
  apply StatMech.Onsager.CellEulerBound.topEdge_injective

/--
[card_topEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellEulerBound.lean)
-/
@[path]
private lemma card_topEdges_eq
  {S : Finset Cell} :
-- imply
  (topEdges S).card = S.card := by
-- proof
  apply StatMech.Onsager.CellEulerBound.card_topEdges S

/--
[topEdges_subset_regEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellEulerBound.lean)
-/
@[path]
private lemma topEdges_subset_regEdges_eq
  {S : Finset Cell} :
-- imply
  topEdges S ⊆ regEdges S := by
-- proof
  apply StatMech.Onsager.CellEulerBound.topEdges_subset_regEdges S

/--
[mem_openTopSkeleton_edgeSet_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellEulerBound.lean)
-/
@[path]
private lemma mem_openTopSkeleton_edgeSet_iff_eq
  {S : Finset Cell}
-- given
  (e : Sym2 {v // v ∈ regVerts S}) :
-- imply
  e ∈ (openTopSkeleton S).edgeSet ↔ Sym2.map Subtype.val e ∈ regEdges S \ topEdges S := by
-- proof
  apply StatMech.Onsager.CellEulerBound.mem_openTopSkeleton_edgeSet_iff S e

/--
[card_openTopSkeleton_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellEulerBound.lean)
-/
@[path]
private lemma card_openTopSkeleton_edges_eq
  {S : Finset Cell} :
-- imply
  Nat.card (openTopSkeleton S).edgeSet = (regEdges S \ topEdges S).card := by
-- proof
  apply StatMech.Onsager.CellEulerBound.card_openTopSkeleton_edges S

/--
[regVerts_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellEulerBound.lean)
-/
@[path]
private lemma regVerts_card_le_eq
  {S : Finset Cell}
-- given
  (hconn : (openTopSkeleton S).Connected) :
-- imply
  (regVerts S).card ≤ (regEdges S \ topEdges S).card + 1 := by
-- proof
  apply StatMech.Onsager.CellEulerBound.regVerts_card_le S hconn

/--
[regChi_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellEulerBound.lean)
-/
@[path]
private lemma regChi_le_one_eq
  {S : Finset Cell}
-- given
  (hconn : (openTopSkeleton S).Connected) :
-- imply
  regChi S ≤ 1 := by
-- proof
  apply StatMech.Onsager.CellEulerBound.regChi_le_one S hconn

/--
[eulerChar_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellEulerBound.lean)
-/
@[path]
private lemma eulerChar_le_one_eq
  {S : Finset Cell}
-- given
  (hconn : (openTopSkeleton S).Connected) :
-- imply
  eulerChar S ≤ 1 := by
-- proof
  apply StatMech.Onsager.CellEulerBound.eulerChar_le_one S hconn


-- created on 2026-10-23
