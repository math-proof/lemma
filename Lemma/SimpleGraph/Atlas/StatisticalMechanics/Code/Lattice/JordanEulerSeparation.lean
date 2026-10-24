import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Lattice.JordanEulerSeparation
open SimpleGraph StatMech StatMech.Lattice


/--
[jes_faceCount_eq_boundedRegionCount_add_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEulerSeparation.lean)
-/
@[path]
private lemma jes_faceCount_eq_boundedRegionCount_add_one_eq
  [Finite V]
  [DecidableEq V]
  {G : SimpleGraph V} :
-- imply
  faceCount G = jes_boundedRegionCount G + 1 := by
-- proof
  apply StatMech.Lattice.jes_faceCount_eq_boundedRegionCount_add_one G

/--
[jes_tree_boundedRegionCount_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEulerSeparation.lean)
-/
@[path]
private lemma jes_tree_boundedRegionCount_zero_eq
  [Finite V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (hG : G.IsAcyclic) :
-- imply
  jes_boundedRegionCount G = 0 := by
-- proof
  apply StatMech.Lattice.jes_tree_boundedRegionCount_zero hG

/--
[jes_closing_edge_boundedRegionCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEulerSeparation.lean)
-/
@[path]
private lemma jes_closing_edge_boundedRegionCount_eq
  [Finite V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {a b : V}
-- given
  (hne : a ≠ b)
  (hadj : ¬ G.Adj a b)
  (hr : G.Reachable a b) :
-- imply
  jes_boundedRegionCount (G ⊔ edge a b) = jes_boundedRegionCount G + 1 := by
-- proof
  apply StatMech.Lattice.jes_closing_edge_boundedRegionCount G hne hadj hr

/--
[jes_closing_edge_one_boundedRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEulerSeparation.lean)
-/
@[path]
private lemma jes_closing_edge_one_boundedRegion_eq
  [Finite V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {a b : V}
-- given
  (hG : G.IsAcyclic)
  (hne : a ≠ b)
  (hadj : ¬ G.Adj a b)
  (hr : G.Reachable a b) :
-- imply
  jes_boundedRegionCount (G ⊔ edge a b) = 1 := by
-- proof
  apply StatMech.Lattice.jes_closing_edge_one_boundedRegion hG hne hadj hr

/--
[jes_closing_edge_faceCount_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEulerSeparation.lean)
-/
@[path]
private lemma jes_closing_edge_faceCount_two_eq
  [Finite V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {a b : V}
-- given
  (hG : G.IsAcyclic)
  (hne : a ≠ b)
  (hadj : ¬ G.Adj a b)
  (hr : G.Reachable a b) :
-- imply
  faceCount (G ⊔ edge a b) = 2 := by
-- proof
  apply StatMech.Lattice.jes_closing_edge_faceCount_two hG hne hadj hr

/--
[jes_connected_nullity_zero_isTree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEulerSeparation.lean)
-/
@[path]
private lemma jes_connected_nullity_zero_isTree_eq
  [Finite V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (hconn : G.Connected)
  (hnull : nullity G = 0) :
-- imply
  G.IsTree := by
-- proof
  apply StatMech.Lattice.jes_connected_nullity_zero_isTree hconn hnull

/--
[jes_exists_closing_edge_of_nullity_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEulerSeparation.lean)
-/
@[path]
private lemma jes_exists_closing_edge_of_nullity_one_eq
  [Finite V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (hnull : nullity G = 1) :
-- imply
  ∃ a b : V, s(a, b) ∈ G.edgeSet ∧ (G.deleteEdges {s(a, b)}).Reachable a b := by
-- proof
  apply StatMech.Lattice.jes_exists_closing_edge_of_nullity_one hnull

/--
[jes_delete_closing_edge_isTree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEulerSeparation.lean)
-/
@[path]
private lemma jes_delete_closing_edge_isTree_eq
  [Finite V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {a b : V}
-- given
  (hconn : G.Connected)
  (hnull : nullity G = 1)
  (he : s(a, b) ∈ G.edgeSet)
  (hr : (G.deleteEdges {s(a, b)}).Reachable a b) :
-- imply
  (G.deleteEdges {s(a, b)}).IsTree := by
-- proof
  apply StatMech.Lattice.jes_delete_closing_edge_isTree hconn hnull he hr

/--
[jes_nullity_one_boundedRegionCount_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEulerSeparation.lean)
-/
@[path]
private lemma jes_nullity_one_boundedRegionCount_one_eq
  [Finite V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (hnull : nullity G = 1) :
-- imply
  jes_boundedRegionCount G = 1 := by
-- proof
  apply StatMech.Lattice.jes_nullity_one_boundedRegionCount_one hnull

/--
[jes_path_edge_ncard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEulerSeparation.lean)
-/
@[path]
private lemma jes_path_edge_ncard_eq
  [Finite V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {u v : V}
  {p : G.Walk u v}
-- given
  (hp : p.IsPath) :
-- imply
  p.edgeSet.ncard = p.length := by
-- proof
  apply StatMech.Lattice.jes_path_edge_ncard p hp

/--
[jes_path_coe_isTree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEulerSeparation.lean)
-/
@[path]
private lemma jes_path_coe_isTree_eq
  [Finite V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {u v : V}
  {p : G.Walk u v}
-- given
  (hp : p.IsPath) :
-- imply
  p.toSubgraph.coe.IsTree := by
-- proof
  apply StatMech.Lattice.jes_path_coe_isTree p hp

/--
[jes_path_coe_acyclic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEulerSeparation.lean)
-/
@[path]
private lemma jes_path_coe_acyclic_eq
  [Finite V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {u v : V}
  {p : G.Walk u v}
-- given
  (hp : p.IsPath) :
-- imply
  p.toSubgraph.coe.IsAcyclic := by
-- proof
  apply StatMech.Lattice.jes_path_coe_acyclic p hp

/--
[jes_path_coe_nullity_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEulerSeparation.lean)
-/
@[path]
private lemma jes_path_coe_nullity_zero_eq
  [Finite V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {u v : V}
  {p : G.Walk u v}
-- given
  (hp : p.IsPath) :
-- imply
  nullity p.toSubgraph.coe = 0 := by
-- proof
  apply StatMech.Lattice.jes_path_coe_nullity_zero p hp

/--
[jes_path_coe_boundedRegionCount_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEulerSeparation.lean)
-/
@[path]
private lemma jes_path_coe_boundedRegionCount_zero_eq
  [Finite V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {u v : V}
  {p : G.Walk u v}
-- given
  (hp : p.IsPath) :
-- imply
  jes_boundedRegionCount p.toSubgraph.coe = 0 := by
-- proof
  apply StatMech.Lattice.jes_path_coe_boundedRegionCount_zero p hp

/--
[jes_path_coe_faceCount_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEulerSeparation.lean)
-/
@[path]
private lemma jes_path_coe_faceCount_one_eq
  [Finite V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {u v : V}
  {p : G.Walk u v}
-- given
  (hp : p.IsPath) :
-- imply
  faceCount p.toSubgraph.coe = 1 := by
-- proof
  apply StatMech.Lattice.jes_path_coe_faceCount_one p hp

/--
[jes_cycle_coe_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEulerSeparation.lean)
-/
@[path]
private lemma jes_cycle_coe_connected_eq
  [Finite V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {w : V}
  {c : G.Walk w w} :
-- imply
  c.toSubgraph.coe.Connected := by
-- proof
  apply StatMech.Lattice.jes_cycle_coe_connected c

/--
[jes_cycle_coe_nullity_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEulerSeparation.lean)
-/
@[path]
private lemma jes_cycle_coe_nullity_one_eq
  [Finite V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {w : V}
  {c : G.Walk w w}
-- given
  (hc : c.IsCycle) :
-- imply
  nullity c.toSubgraph.coe = 1 := by
-- proof
  apply StatMech.Lattice.jes_cycle_coe_nullity_one c hc

/--
[jes_cycle_delete_edge_isTree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEulerSeparation.lean)
-/
@[path]
private lemma jes_cycle_delete_edge_isTree_eq
  [Finite V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {w : V}
  {c : G.Walk w w}
-- given
  (hc : c.IsCycle) :
-- imply
  ∃ (a b : ↑c.toSubgraph.verts), s(a, b) ∈ c.toSubgraph.coe.edgeSet ∧ (c.toSubgraph.coe.deleteEdges {s(a, b)}).Reachable a b ∧ (c.toSubgraph.coe.deleteEdges {s(a, b)}).IsTree ∧ c.toSubgraph.coe = (c.toSubgraph.coe.deleteEdges {s(a, b)}) ⊔ edge a b := by
-- proof
  apply StatMech.Lattice.jes_cycle_delete_edge_isTree c hc

/--
[jes_cycle_boundedRegionCount_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEulerSeparation.lean)
-/
@[path]
private lemma jes_cycle_boundedRegionCount_one_eq
  [Finite V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {w : V}
  {c : G.Walk w w}
-- given
  (hc : c.IsCycle) :
-- imply
  jes_boundedRegionCount c.toSubgraph.coe = 1 := by
-- proof
  apply StatMech.Lattice.jes_cycle_boundedRegionCount_one c hc

/--
[jes_cycle_faceCount_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEulerSeparation.lean)
-/
@[path]
private lemma jes_cycle_faceCount_two_eq
  [Finite V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {w : V}
  {c : G.Walk w w}
-- given
  (hc : c.IsCycle) :
-- imply
  faceCount c.toSubgraph.coe = 2 := by
-- proof
  apply StatMech.Lattice.jes_cycle_faceCount_two c hc

/--
[jes_cycle_is_tree_plus_closing_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEulerSeparation.lean)
-/
@[path]
private lemma jes_cycle_is_tree_plus_closing_edge_eq
  [Finite V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {w : V}
  {c : G.Walk w w}
-- given
  (hc : c.IsCycle) :
-- imply
  ∃ (a b : ↑c.toSubgraph.verts), (c.toSubgraph.coe.deleteEdges {s(a, b)}).IsTree ∧ c.toSubgraph.coe = (c.toSubgraph.coe.deleteEdges {s(a, b)}) ⊔ edge a b ∧ jes_boundedRegionCount (c.toSubgraph.coe.deleteEdges {s(a, b)}) = 0 ∧ jes_boundedRegionCount c.toSubgraph.coe = 1 := by
-- proof
  apply StatMech.Lattice.jes_cycle_is_tree_plus_closing_edge c hc


-- created on 2026-10-23
