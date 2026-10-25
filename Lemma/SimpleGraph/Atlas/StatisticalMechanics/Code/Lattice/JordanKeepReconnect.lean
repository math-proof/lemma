import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Lattice.JordanKeepReconnect.Part2
open SimpleGraph Set StatMech StatMech.Lattice


/--
[jkr_lineH_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanKeepReconnect.lean)
-/
@[path]
private lemma jkr_lineH_adj_eq
  {a b : Site 2} :
-- imply
  jkr_lineH.Adj a b ↔ (hypercubicLattice 2).Adj a b ∧ a 1 = 0 ∧ b 1 = 0 ∧ ¬ ({a 0, b 0} = ({0, 1} : Finset ℤ)) := by
-- proof
  apply StatMech.Lattice.jkr_lineH_adj a b

/--
[jkr_pair_eq_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanKeepReconnect.lean)
-/
@[path]
private lemma jkr_pair_eq_iff_eq
  {c d : ℤ}
-- given
  (hne : c ≠ d) :
-- imply
  ({c, d} = ({0, 1} : Finset ℤ)) ↔ ((c = 0 ∧ d = 1) ∨ (c = 1 ∧ d = 0)) := by
-- proof
  apply StatMech.Lattice.jkr_pair_eq_iff c d hne

/--
[jkr_wall_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanKeepReconnect.lean)
-/
@[path]
private lemma jkr_wall_not_mem_eq :
-- imply
  s(![(0:ℤ), 0], ![(1:ℤ), 0]) ∉ jkr_lineH.edgeSet := by
-- proof
  apply StatMech.Lattice.jkr_wall_not_mem

/--
[jkr_edge_on_line](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanKeepReconnect.lean)
-/
@[path]
private lemma jkr_edge_on_line_eq
  {a b : Site 2}
-- given
  (h : jkr_lineH.Adj a b) :
-- imply
  a 1 = 0 ∧ b 1 = 0 := by
-- proof
  apply StatMech.Lattice.jkr_edge_on_line h

/--
[jkr_edge_x](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanKeepReconnect.lean)
-/
@[path]
private lemma jkr_edge_x_eq
  {a b : Site 2}
-- given
  (h : jkr_lineH.Adj a b) :
-- imply
  (a 0 = b 0 + 1 ∨ b 0 = a 0 + 1) ∧ ¬ ({a 0, b 0} = ({0, 1} : Finset ℤ)) := by
-- proof
  apply StatMech.Lattice.jkr_edge_x h

/--
[jkr_edge_sameSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanKeepReconnect.lean)
-/
@[path]
private lemma jkr_edge_sameSide_eq
  {a b : Site 2}
-- given
  (h : jkr_lineH.Adj a b) :
-- imply
  (a 0 ≤ 0 ↔ b 0 ≤ 0) := by
-- proof
  apply StatMech.Lattice.jkr_edge_sameSide h

/--
[jkr_walk_sameSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanKeepReconnect.lean)
-/
@[path]
private lemma jkr_walk_sameSide_eq
  {x y : Site 2}
  {w : jkr_lineH.Walk x y} :
-- imply
  (x 0 ≤ 0 ↔ y 0 ≤ 0) := by
-- proof
  apply StatMech.Lattice.jkr_walk_sameSide w

/--
[jkr_pq_not_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanKeepReconnect.lean)
-/
@[path]
private lemma jkr_pq_not_reachable_eq :
-- imply
  ¬ jkr_lineH.Reachable ![(0:ℤ), 0] ![(1:ℤ), 0] := by
-- proof
  apply StatMech.Lattice.jkr_pq_not_reachable

/--
[jkr_shared_vstep_line](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanKeepReconnect.lean)
-/
@[path]
private lemma jkr_shared_vstep_line_eq
  {a : ℤ} :
-- imply
  sharedPrimalEdge ![a, (0:ℤ)] ![a, -1] = s(![a, (0:ℤ)], ![a + 1, 0]) := by
-- proof
  apply StatMech.Lattice.jkr_shared_vstep_line a

/--
[jkr_line_seg_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanKeepReconnect.lean)
-/
@[path]
private lemma jkr_line_seg_mem_eq
  {a : ℤ} :
-- imply
  s(![a, (0:ℤ)], ![a + 1, 0]) ∈ jkr_lineH.edgeSet ↔ a ≠ 0 := by
-- proof
  apply StatMech.Lattice.jkr_line_seg_mem a

/--
[jkr_deleted_edge_sameSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanKeepReconnect.lean)
-/
@[path]
private lemma jkr_deleted_edge_sameSide_eq
  {a b : Site 2}
-- given
  (h : ((whb_faceRegion jkr_lineH).deleteEdges {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Adj a b) :
-- imply
  (0 ≤ a 1 ↔ 0 ≤ b 1) := by
-- proof
  apply StatMech.Lattice.jkr_deleted_edge_sameSide h

/--
[jkr_deleted_walk_sameSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanKeepReconnect.lean)
-/
@[path]
private lemma jkr_deleted_walk_sameSide_eq
  {x y : Site 2}
  {w : ((whb_faceRegion jkr_lineH).deleteEdges {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Walk x y} :
-- imply
  (0 ≤ x 1 ↔ 0 ≤ y 1) := by
-- proof
  apply StatMech.Lattice.jkr_deleted_walk_sameSide w

/--
[jkr_faces_not_reconnect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanKeepReconnect.lean)
-/
@[path]
private lemma jkr_faces_not_reconnect_eq :
-- imply
  ¬ ((whb_faceRegion jkr_lineH).deleteEdges {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable ![(0:ℤ), 0] ![(0:ℤ), -1] := by
-- proof
  apply StatMech.Lattice.jkr_faces_not_reconnect

/--
[jkr_instance_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanKeepReconnect.lean)
-/
@[path]
private lemma jkr_instance_valid_eq :
-- imply
  (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(1:ℤ), 0] ∧ s(![(0:ℤ), 0], ![(1:ℤ), 0]) ∉ jkr_lineH.edgeSet ∧ (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(0:ℤ), -1] ∧ sharedPrimalEdge ![(0:ℤ), 0] ![(0:ℤ), -1] = s(![(0:ℤ), 0], ![(1:ℤ), 0]) := by
-- proof
  apply StatMech.Lattice.jkr_instance_valid

/--
[jkr_keepReconnectResidue_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanKeepReconnect.lean)
-/
@[path]
private lemma jkr_keepReconnectResidue_false_eq :
-- imply
  ¬ jwn_KeepReconnectResidue := by
-- proof
  apply StatMech.Lattice.jkr_keepReconnectResidue_false

/--
[jkr_witness_bot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanKeepReconnect.lean)
-/
@[path]
private lemma jkr_witness_bot_eq :
-- imply
  (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(1:ℤ), 0] ∧ s(![(0:ℤ), 0], ![(1:ℤ), 0]) ∉ (⊥ : SimpleGraph (Site 2)).edgeSet ∧ (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(0:ℤ), -1] ∧ sharedPrimalEdge ![(0:ℤ), 0] ![(0:ℤ), -1] = s(![(0:ℤ), 0], ![(1:ℤ), 0]) ∧ ¬ (⊥ : SimpleGraph (Site 2)).Reachable ![(0:ℤ), 0] ![(1:ℤ), 0] ∧ ((whb_faceRegion (⊥ : SimpleGraph (Site 2))).deleteEdges {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable ![(0:ℤ), 0] ![(0:ℤ), -1] := by
-- proof
  apply StatMech.Lattice.jkr_witness_bot

/--
[jkr_witness_square](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanKeepReconnect.lean)
-/
@[path]
private lemma jkr_witness_square_eq :
-- imply
  (hypercubicLattice 2).Adj (jbc_Pce.emb jbc_v0) (jbc_Pce.emb jbc_v1) ∧ s(jbc_Pce.emb jbc_v0, jbc_Pce.emb jbc_v1) ∉ (jei_pushGraph jbc_Pce ⊥).edgeSet ∧ (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(0:ℤ), -1] ∧ sharedPrimalEdge ![(0:ℤ), 0] ![(0:ℤ), -1] = s(jbc_Pce.emb jbc_v0, jbc_Pce.emb jbc_v1) ∧ ¬ (jei_pushGraph jbc_Pce ⊥).Reachable (jbc_Pce.emb jbc_v0) (jbc_Pce.emb jbc_v1) ∧ ((whb_faceRegion (jei_pushGraph jbc_Pce ⊥)).deleteEdges {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable ![(0:ℤ), 0] ![(0:ℤ), -1] := by
-- proof
  apply StatMech.Lattice.jkr_witness_square

/--
[jkr_witness_ring](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanKeepReconnect.lean)
-/
@[path]
private lemma jkr_witness_ring_eq :
-- imply
  jkd_ringP.G.Adj jkd_r0 jkd_r1 ∧ s(jkd_ringP.emb jkd_r0, jkd_ringP.emb jkd_r1) ∉ (jei_pushGraph jkd_ringP ⊥).edgeSet ∧ (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(0:ℤ), -1] ∧ sharedPrimalEdge ![(0:ℤ), 0] ![(0:ℤ), -1] = s(jkd_ringP.emb jkd_r0, jkd_ringP.emb jkd_r1) ∧ ¬ (jei_pushGraph jkd_ringP ⊥).Reachable (jkd_ringP.emb jkd_r0) (jkd_ringP.emb jkd_r1) ∧ ((whb_faceRegion (jei_pushGraph jkd_ringP ⊥)).deleteEdges {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable ![(0:ℤ), 0] ![(0:ℤ), -1] := by
-- proof
  apply StatMech.Lattice.jkr_witness_ring

/--
[jkr_finite_of_keepReconnect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanKeepReconnect.lean)
-/
@[path]
private lemma jkr_finite_of_keepReconnect_eq
-- given
  (hres : jwn_KeepReconnectResidue) :
-- imply
  jkr_FiniteKeepReconnectResidue := by
-- proof
  apply StatMech.Lattice.jkr_finite_of_keepReconnect hres

/--
[jkr_lineH_edgeSet_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanKeepReconnect.lean)
-/
@[path]
private lemma jkr_lineH_edgeSet_infinite_eq :
-- imply
  jkr_lineH.edgeSet.Infinite := by
-- proof
  apply StatMech.Lattice.jkr_lineH_edgeSet_infinite

/--
[jkr_lineH_not_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanKeepReconnect.lean)
-/
@[path]
private lemma jkr_lineH_not_finite_eq :
-- imply
  ¬ jkr_lineH.edgeSet.Finite := by
-- proof
  apply StatMech.Lattice.jkr_lineH_not_finite

/--
[jkr_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanKeepReconnect.lean)
-/
@[path]
private lemma jkr_status_eq :
-- imply
  ¬ jwn_KeepReconnectResidue ∧ (¬ jkr_lineH.Reachable ![(0:ℤ), 0] ![(1:ℤ), 0] ∧ ¬ ((whb_faceRegion jkr_lineH).deleteEdges {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable ![(0:ℤ), 0] ![(0:ℤ), -1]) ∧ jkr_lineH.edgeSet.Infinite ∧ (jwn_KeepReconnectResidue → jkr_FiniteKeepReconnectResidue) := by
-- proof
  apply StatMech.Lattice.jkr_status


-- created on 2026-10-23
