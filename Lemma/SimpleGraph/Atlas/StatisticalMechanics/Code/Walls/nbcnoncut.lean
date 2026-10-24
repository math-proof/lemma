import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.nbcnoncut
open Finset Set SimpleGraph StatMech StatMech.Walls


/--
[nbc_induce_adj_of_latticeOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/nbcnoncut.lean)
-/
@[path]
private lemma nbc_induce_adj_of_latticeOn_eq
  {K : Set (Site 2)}
  {x y : Site 2}
-- given
  (hx : x ∈ K)
  (hy : y ∈ K)
  (h : (latticeOn K).Adj x y) :
-- imply
  ((hypercubicLattice 2).induce K).Adj ⟨x, hx⟩ ⟨y, hy⟩ := by
-- proof
  apply StatMech.Walls.nbc_induce_adj_of_latticeOn hx hy h

/--
[nbc_induce_reachable_of_latticeOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/nbcnoncut.lean)
-/
@[path]
private lemma nbc_induce_reachable_of_latticeOn_eq
  {K : Set (Site 2)} :
-- imply
  ∀ {x y : Site 2} (hx : x ∈ K) (hy : y ∈ K), (latticeOn K).Walk x y → ((hypercubicLattice 2).induce K).Reachable ⟨x, hx⟩ ⟨y, hy⟩ := by
-- proof
  apply StatMech.Walls.nbc_induce_reachable_of_latticeOn

/--
[nbc_cellConnected_of_isConnectedCluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/nbcnoncut.lean)
-/
@[path]
private lemma nbc_cellConnected_of_isConnectedCluster_eq
  {K : Finset (Site 2)}
-- given
  (h : IsConnectedCluster K) :
-- imply
  CellConnected (↑K : Set (Site 2)) := by
-- proof
  apply StatMech.Walls.nbc_cellConnected_of_isConnectedCluster h

/--
[nbc_isConnectedCluster_of_cellConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/nbcnoncut.lean)
-/
@[path]
private lemma nbc_isConnectedCluster_of_cellConnected_eq
  {J : Finset (Site 2)}
-- given
  (hoJ : origin 2 ∈ J)
  (h : CellConnected (↑J : Set (Site 2))) :
-- imply
  IsConnectedCluster J := by
-- proof
  apply StatMech.Walls.nbc_isConnectedCluster_of_cellConnected hoJ h

/--
[nbc_tree_two_leaves](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/nbcnoncut.lean)
-/
@[path]
private lemma nbc_tree_two_leaves_eq
  [Fintype V]
  {T : SimpleGraph V}
  [DecidableRel T.Adj]
-- given
  (hT : T.IsTree)
  (hn : 2 ≤ Fintype.card V) :
-- imply
  ∃ a b : V, a ≠ b ∧ T.degree a = 1 ∧ T.degree b = 1 := by
-- proof
  apply StatMech.Walls.nbc_tree_two_leaves T hT hn

/--
[nbc_induce_mono_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/nbcnoncut.lean)
-/
@[path]
private lemma nbc_induce_mono_left_eq
  {T G : SimpleGraph V}
  {s : Set V}
-- given
  (hle : T ≤ G) :
-- imply
  T.induce s ≤ G.induce s := by
-- proof
  apply StatMech.Walls.nbc_induce_mono_left s hle

/--
[nbc_cellConnected_diff_of_treeCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/nbcnoncut.lean)
-/
@[path]
private lemma nbc_cellConnected_diff_of_treeCut_eq
  {K : Finset (Site 2)}
  {T : SimpleGraph (↑(↑K : Set (Site 2)))}
  {v : ↑(↑K : Set (Site 2))}
-- given
  (hle : T ≤ (hypercubicLattice 2).induce (↑K : Set (Site 2)))
  (h0 : (T.induce ({v}ᶜ : Set _)).Connected) :
-- imply
  CellConnected ((↑K : Set (Site 2)) \ {v.1}) := by
-- proof
  apply StatMech.Walls.nbc_cellConnected_diff_of_treeCut hle h0

/--
[nbc_two_noncut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/nbcnoncut.lean)
-/
@[path]
private lemma nbc_two_noncut_eq
  {K : Finset (Site 2)}
-- given
  (hcard : 2 ≤ K.card)
  (hconn : CellConnected (↑K : Set (Site 2))) :
-- imply
  ∃ a ∈ K, ∃ b ∈ K, a ≠ b ∧ CellConnected ((↑K : Set (Site 2)) \ {a}) ∧ CellConnected ((↑K : Set (Site 2)) \ {b}) := by
-- proof
  apply StatMech.Walls.nbc_two_noncut hcard hconn

/--
[nbc_exists_noncut_ne_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/nbcnoncut.lean)
-/
@[path]
private lemma nbc_exists_noncut_ne_origin_eq
  {K : Finset (Site 2)}
-- given
  (hcard : 2 ≤ K.card)
  (hconn : CellConnected (↑K : Set (Site 2))) :
-- imply
  ∃ c ∈ K, c ≠ origin 2 ∧ CellConnected ((↑K : Set (Site 2)) \ {c}) := by
-- proof
  apply StatMech.Walls.nbc_exists_noncut_ne_origin hcard hconn

/--
[nbc_coe_erase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/nbcnoncut.lean)
-/
@[path]
private lemma nbc_coe_erase_eq
  {K : Finset (Site 2)}
  {c : Site 2} :
-- imply
  (↑(K.erase c) : Set (Site 2)) = (↑K : Set (Site 2)) \ {c} := by
-- proof
  apply StatMech.Walls.nbc_coe_erase K c

/--
[nbc_isConnectedCluster_erase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/nbcnoncut.lean)
-/
@[path]
private lemma nbc_isConnectedCluster_erase_eq
  {K : Finset (Site 2)}
  {c : Site 2}
-- given
  (ho : origin 2 ∈ K)
  (hcorigin : c ≠ origin 2)
  (h : CellConnected ((↑K : Set (Site 2)) \ {c})) :
-- imply
  IsConnectedCluster (K.erase c) := by
-- proof
  apply StatMech.Walls.nbc_isConnectedCluster_erase ho hcorigin h

/--
[nbc_atc_of_boundaryNonCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/nbcnoncut.lean)
-/
@[path]
private lemma nbc_atc_of_boundaryNonCut_eq
-- given
  (h : nbc_BoundaryNonCutExists) :
-- imply
  atc_HasRemovableConnCell := by
-- proof
  apply StatMech.Walls.nbc_atc_of_boundaryNonCut h

/--
[nbc_fbc_hasRemovableCell_of_boundaryNonCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/nbcnoncut.lean)
-/
@[path]
private lemma nbc_fbc_hasRemovableCell_of_boundaryNonCut_eq
-- given
  (h : nbc_BoundaryNonCutExists) :
-- imply
  fbc_HasRemovableCell := by
-- proof
  apply StatMech.Walls.nbc_fbc_hasRemovableCell_of_boundaryNonCut h

/--
[nbc_pendant_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/nbcnoncut.lean)
-/
@[path]
private lemma nbc_pendant_boundary_eq
  {K : Finset (Site 2)}
  {c : Site 2}
-- given
  (hpend : jc_IsPendantCell (↑K : Set (Site 2)) c) :
-- imply
  ∃ n ∉ K, (hypercubicLattice 2).Adj c n := by
-- proof
  apply StatMech.Walls.nbc_pendant_boundary hpend

/--
[nbc_boundaryNonCut_of_pendant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/nbcnoncut.lean)
-/
@[path]
private lemma nbc_boundaryNonCut_of_pendant_eq
  {K : Finset (Site 2)}
  {c : Site 2}
-- given
  (hconn : IsConnectedCluster K)
  (hcorigin : c ≠ origin 2)
  (hpend : jc_IsPendantCell (↑K : Set (Site 2)) c) :
-- imply
  ∃ c ∈ K, c ≠ origin 2 ∧ (∃ n ∉ K, (hypercubicLattice 2).Adj c n) ∧ CellConnected ((↑K : Set (Site 2)) \ {c}) := by
-- proof
  apply StatMech.Walls.nbc_boundaryNonCut_of_pendant hconn hcorigin hpend

/--
[nbc_tromino_pendant_10](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/nbcnoncut.lean)
-/
@[path]
private lemma nbc_tromino_pendant_10_eq :
-- imply
  jc_IsPendantCell (↑pc2_tromino : Set (Site 2)) ![1, 0] := by
-- proof
  apply StatMech.Walls.nbc_tromino_pendant_10

/--
[nbc_tromino_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/nbcnoncut.lean)
-/
@[path]
private lemma nbc_tromino_nonvacuous_eq :
-- imply
  ∃ c ∈ pc2_tromino, c ≠ origin 2 ∧ (∃ n ∉ pc2_tromino, (hypercubicLattice 2).Adj c n) ∧ CellConnected ((↑pc2_tromino : Set (Site 2)) \ {c}) := by
-- proof
  apply StatMech.Walls.nbc_tromino_nonvacuous


-- created on 2026-10-23
