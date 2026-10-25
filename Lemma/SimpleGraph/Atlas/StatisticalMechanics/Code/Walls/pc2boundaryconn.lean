import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.pc2boundaryconn.Part4
open Finset Set SimpleGraph StatMech StatMech.Lattice


/--
[pc2_box_faceBoundaryConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/pc2boundaryconn.lean)
-/
@[path]
private lemma pc2_box_faceBoundaryConnected_eq
  {m n : ℕ} :
-- imply
  FaceBoundaryConnected (↑(boxCluster m n)) (boxFrame m n) := by
-- proof
  apply StatMech.Lattice.pc2_box_faceBoundaryConnected m n

/--
[pc2_faceBoundaryConnected_of_anchor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/pc2boundaryconn.lean)
-/
@[path]
private lemma pc2_faceBoundaryConnected_of_anchor_eq
  {K : Set (Site 2)}
  {T : Finset (Site 2)}
  {a₀ : Site 2}
-- given
  (ha₀ : a₀ ∈ T)
  (hwalk : ∀ f ∈ T, ∃ p : (faceBoundaryGraph K).Walk a₀ f, ∀ v ∈ p.support, v ∈ T) :
-- imply
  FaceBoundaryConnected K T := by
-- proof
  apply StatMech.Lattice.pc2_faceBoundaryConnected_of_anchor ha₀ hwalk

/--
[pc2_box_faceBoundaryConnected_via_anchor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/pc2boundaryconn.lean)
-/
@[path]
private lemma pc2_box_faceBoundaryConnected_via_anchor_eq
  {m n : ℕ} :
-- imply
  FaceBoundaryConnected (↑(boxCluster m n)) (boxFrame m n) := by
-- proof
  apply StatMech.Lattice.pc2_box_faceBoundaryConnected_via_anchor m n

/--
[pc2_single_dualCircuit_of_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/pc2boundaryconn.lean)
-/
@[path]
private lemma pc2_single_dualCircuit_of_residue_eq
  {K : Finset (Site 2)}
  {f₀ : Site 2}
-- given
  (h : pc2_BoundaryConnGivenHoleFree)
  (hconn : IsConnectedCluster K)
  (hhf : pc2_HoleFree (↑K : Set (Site 2)))
  (hfin : (↑K : Set (Site 2)).Finite)
  (hf₀ : f₀ ∈ (boundarySupport hfin : Set (Site 2))) :
-- imply
  ∃ c : (faceBoundaryGraph (↑K : Set (Site 2))).Walk f₀ f₀, c.IsTrail ∧ ∀ e ∈ (faceBoundaryGraph (↑K : Set (Site 2))).edgeSet, e ∈ c.edges := by
-- proof
  apply StatMech.Lattice.pc2_single_dualCircuit_of_residue h K hconn hhf hfin hf₀

/--
[pc2_mem_tromino](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/pc2boundaryconn.lean)
-/
@[path]
private lemma pc2_mem_tromino_eq
  {p q : ℤ} :
-- imply
  (![p, q] : Site 2) ∈ (↑pc2_tromino : Set (Site 2)) ↔ (p = 0 ∧ q = 0) ∨ (p = 1 ∧ q = 0) ∨ (p = 0 ∧ q = 1) := by
-- proof
  apply StatMech.Lattice.pc2_mem_tromino p q

/--
[pc2_origin_mem_tromino](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/pc2boundaryconn.lean)
-/
@[path]
private lemma pc2_origin_mem_tromino_eq :
-- imply
  origin 2 ∈ pc2_tromino := by
-- proof
  apply StatMech.Lattice.pc2_origin_mem_tromino

/--
[pc2_tromino_isConnectedCluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/pc2boundaryconn.lean)
-/
@[path]
private lemma pc2_tromino_isConnectedCluster_eq :
-- imply
  IsConnectedCluster pc2_tromino := by
-- proof
  apply StatMech.Lattice.pc2_tromino_isConnectedCluster

/--
[pc2_bdEdge_trom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/pc2boundaryconn.lean)
-/
@[path]
private lemma pc2_bdEdge_trom_eq
  {p q : Site 2}
-- given
  (hp : p ∈ (↑pc2_tromino : Set (Site 2)))
  (hq : q ∉ (↑pc2_tromino : Set (Site 2))) :
-- imply
  bdEdge (↑pc2_tromino : Set (Site 2)) s(p, q) := by
-- proof
  apply StatMech.Lattice.pc2_bdEdge_trom hp hq

/--
[pc2_trom_adj_1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/pc2boundaryconn.lean)
-/
@[path]
private lemma pc2_trom_adj_1_eq :
-- imply
  (faceBoundaryGraph (↑pc2_tromino : Set (Site 2))).Adj ![(-1:ℤ), -1] ![(0:ℤ), -1] := by
-- proof
  apply StatMech.Lattice.pc2_trom_adj_1

/--
[pc2_trom_adj_2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/pc2boundaryconn.lean)
-/
@[path]
private lemma pc2_trom_adj_2_eq :
-- imply
  (faceBoundaryGraph (↑pc2_tromino : Set (Site 2))).Adj ![(0:ℤ), -1] ![(1:ℤ), -1] := by
-- proof
  apply StatMech.Lattice.pc2_trom_adj_2

/--
[pc2_trom_adj_3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/pc2boundaryconn.lean)
-/
@[path]
private lemma pc2_trom_adj_3_eq :
-- imply
  (faceBoundaryGraph (↑pc2_tromino : Set (Site 2))).Adj ![(1:ℤ), -1] ![(1:ℤ), 0] := by
-- proof
  apply StatMech.Lattice.pc2_trom_adj_3

/--
[pc2_trom_adj_4](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/pc2boundaryconn.lean)
-/
@[path]
private lemma pc2_trom_adj_4_eq :
-- imply
  (faceBoundaryGraph (↑pc2_tromino : Set (Site 2))).Adj ![(1:ℤ), 0] ![(0:ℤ), 0] := by
-- proof
  apply StatMech.Lattice.pc2_trom_adj_4

/--
[pc2_trom_adj_5](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/pc2boundaryconn.lean)
-/
@[path]
private lemma pc2_trom_adj_5_eq :
-- imply
  (faceBoundaryGraph (↑pc2_tromino : Set (Site 2))).Adj ![(0:ℤ), 0] ![(0:ℤ), 1] := by
-- proof
  apply StatMech.Lattice.pc2_trom_adj_5

/--
[pc2_trom_adj_6](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/pc2boundaryconn.lean)
-/
@[path]
private lemma pc2_trom_adj_6_eq :
-- imply
  (faceBoundaryGraph (↑pc2_tromino : Set (Site 2))).Adj ![(0:ℤ), 1] ![(-1:ℤ), 1] := by
-- proof
  apply StatMech.Lattice.pc2_trom_adj_6

/--
[pc2_trom_adj_7](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/pc2boundaryconn.lean)
-/
@[path]
private lemma pc2_trom_adj_7_eq :
-- imply
  (faceBoundaryGraph (↑pc2_tromino : Set (Site 2))).Adj ![(-1:ℤ), 1] ![(-1:ℤ), 0] := by
-- proof
  apply StatMech.Lattice.pc2_trom_adj_7

/--
[pc2_trom_adj_8](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/pc2boundaryconn.lean)
-/
@[path]
private lemma pc2_trom_adj_8_eq :
-- imply
  (faceBoundaryGraph (↑pc2_tromino : Set (Site 2))).Adj ![(-1:ℤ), 0] ![(-1:ℤ), -1] := by
-- proof
  apply StatMech.Lattice.pc2_trom_adj_8

/--
[pc2_mem_tromFrame_corner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/pc2boundaryconn.lean)
-/
@[path]
private lemma pc2_mem_tromFrame_corner_eq :
-- imply
  (![(-1:ℤ), -1] : Site 2) ∈ pc2_tromFrame := by
-- proof
  apply StatMech.Lattice.pc2_mem_tromFrame_corner

/--
[pc2_tromFrame_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/pc2boundaryconn.lean)
-/
@[path]
private lemma pc2_tromFrame_cases_eq
  {v : Site 2}
-- given
  (hv : v ∈ pc2_tromFrame) :
-- imply
  v = ![(-1:ℤ), -1] ∨ v = ![(0:ℤ), -1] ∨ v = ![(1:ℤ), -1] ∨ v = ![(1:ℤ), 0] ∨ v = ![(0:ℤ), 0] ∨ v = ![(0:ℤ), 1] ∨ v = ![(-1:ℤ), 1] ∨ v = ![(-1:ℤ), 0] := by
-- proof
  apply StatMech.Lattice.pc2_tromFrame_cases hv

/--
[pc2_tromFrame_walk_from_corner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/pc2boundaryconn.lean)
-/
@[path]
private lemma pc2_tromFrame_walk_from_corner_eq
  {v : Site 2}
-- given
  (hv : v ∈ pc2_tromFrame) :
-- imply
  ∃ p : (faceBoundaryGraph (↑pc2_tromino : Set (Site 2))).Walk ![(-1:ℤ), -1] v, ∀ w ∈ p.support, w ∈ pc2_tromFrame := by
-- proof
  apply StatMech.Lattice.pc2_tromFrame_walk_from_corner hv

/--
[pc2_tromino_faceBoundaryConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/pc2boundaryconn.lean)
-/
@[path]
private lemma pc2_tromino_faceBoundaryConnected_eq :
-- imply
  FaceBoundaryConnected (↑pc2_tromino : Set (Site 2)) pc2_tromFrame := by
-- proof
  apply StatMech.Lattice.pc2_tromino_faceBoundaryConnected


-- created on 2026-10-23
