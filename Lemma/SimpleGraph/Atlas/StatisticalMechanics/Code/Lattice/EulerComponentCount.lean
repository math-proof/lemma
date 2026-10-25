import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Lattice.EulerComponentCount.Part2
open SimpleGraph Set StatMech StatMech.Lattice


/--
[ecc_deleteEdge_card_nonbridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerComponentCount.lean)
-/
@[path]
private lemma ecc_deleteEdge_card_nonbridge_eq
  [Empty.Finite V]
  [DecidableEq V]
  {A : SimpleGraph V}
  {a b : V}
-- given
  (he : s(a, b) ∈ A.edgeSet)
  (hr : (A.deleteEdges {s(a, b)}).Reachable a b) :
-- imply
  Nat.card (A.deleteEdges {s(a, b)}).ConnectedComponent = Nat.card A.ConnectedComponent := by
-- proof
  apply StatMech.Lattice.ecc_deleteEdge_card_nonbridge A he hr

/--
[ecc_deleteEdge_card_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerComponentCount.lean)
-/
@[path]
private lemma ecc_deleteEdge_card_bridge_eq
  [Empty.Finite V]
  [DecidableEq V]
  {A : SimpleGraph V}
  {a b : V}
-- given
  (he : s(a, b) ∈ A.edgeSet)
  (hr : ¬ (A.deleteEdges {s(a, b)}).Reachable a b) :
-- imply
  Nat.card (A.deleteEdges {s(a, b)}).ConnectedComponent = Nat.card A.ConnectedComponent + 1 := by
-- proof
  apply StatMech.Lattice.ecc_deleteEdge_card_bridge A he hr

/--
[ecc_deleteEdge_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerComponentCount.lean)
-/
@[path]
private lemma ecc_deleteEdge_card_le_eq
  [Empty.Finite V]
  [DecidableEq V]
  {A : SimpleGraph V}
  {e : Sym2 V} :
-- imply
  Nat.card (A.deleteEdges {e}).ConnectedComponent ≤ Nat.card A.ConnectedComponent + 1 := by
-- proof
  apply StatMech.Lattice.ecc_deleteEdge_card_le A e

/--
[ecc_deleteEdge_card_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerComponentCount.lean)
-/
@[path]
private lemma ecc_deleteEdge_card_ge_eq
  [Empty.Finite V]
  [DecidableEq V]
  {A : SimpleGraph V}
  {e : Sym2 V} :
-- imply
  Nat.card A.ConnectedComponent ≤ Nat.card (A.deleteEdges {e}).ConnectedComponent := by
-- proof
  apply StatMech.Lattice.ecc_deleteEdge_card_ge A e

/--
[ecc_deleteEdges_finset_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerComponentCount.lean)
-/
@[path]
private lemma ecc_deleteEdges_finset_card_le_eq
  [Empty.Finite V]
  [DecidableEq V]
  {A : SimpleGraph V}
  {B : Finset (Sym2 V)} :
-- imply
  Nat.card (A.deleteEdges ↑B).ConnectedComponent ≤ Nat.card A.ConnectedComponent + B.card := by
-- proof
  apply StatMech.Lattice.ecc_deleteEdges_finset_card_le A B

/--
[ecc_comp_add_edges_eq_card_add_nullity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerComponentCount.lean)
-/
@[path]
private lemma ecc_comp_add_edges_eq_card_add_nullity_eq
  [Empty.Finite V]
  [DecidableEq V]
  {A : SimpleGraph V} :
-- imply
  Nat.card A.ConnectedComponent + A.edgeSet.ncard = Nat.card V + nullity A := by
-- proof
  apply StatMech.Lattice.ecc_comp_add_edges_eq_card_add_nullity A

/--
[ecc_two_components_tree_plus_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerComponentCount.lean)
-/
@[path]
private lemma ecc_two_components_tree_plus_bridge_eq
  [Empty.Finite V]
  [DecidableEq V]
  {A : SimpleGraph V}
  {B' : Set (Sym2 V)}
  {a b : V}
-- given
  (hconn : (A.deleteEdges B').Connected)
  (he : s(a, b) ∈ (A.deleteEdges B').edgeSet)
  (hbridge : ¬ ((A.deleteEdges B').deleteEdges {s(a, b)}).Reachable a b) :
-- imply
  Nat.card ((A.deleteEdges B').deleteEdges {s(a, b)}).ConnectedComponent = 2 := by
-- proof
  apply StatMech.Lattice.ecc_two_components_tree_plus_bridge A B' hconn he hbridge

/--
[ecc_bridge_adds_one_component](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerComponentCount.lean)
-/
@[path]
private lemma ecc_bridge_adds_one_component_eq
  [Empty.Finite V]
  [DecidableEq V]
  {A : SimpleGraph V}
  {B' : Set (Sym2 V)}
  {a b : V}
-- given
  (he : s(a, b) ∈ (A.deleteEdges B').edgeSet)
  (hbridge : ¬ ((A.deleteEdges B').deleteEdges {s(a, b)}).Reachable a b) :
-- imply
  Nat.card ((A.deleteEdges B').deleteEdges {s(a, b)}).ConnectedComponent = Nat.card (A.deleteEdges B').ConnectedComponent + 1 := by
-- proof
  apply StatMech.Lattice.ecc_bridge_adds_one_component A B' he hbridge

/--
[ecc_two_components_of_dualModel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerComponentCount.lean)
-/
@[path]
private lemma ecc_two_components_of_dualModel_eq
  [Empty.Finite V]
  [DecidableEq V]
  {A : SimpleGraph V}
  {B' : Set (Sym2 V)}
  {a b : V}
-- given
  (h : ecc_DualCutModel A B' a b) :
-- imply
  Nat.card ((A.deleteEdges B').deleteEdges {s(a, b)}).ConnectedComponent = 2 := by
-- proof
  apply StatMech.Lattice.ecc_two_components_of_dualModel A B' h

/--
[ecc_cycle_dual_two_components](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerComponentCount.lean)
-/
@[path]
private lemma ecc_cycle_dual_two_components_eq
  [Empty.Finite V]
  [DecidableEq V]
  [Empty.Finite W]
  [DecidableEq W]
  {G : SimpleGraph W}
  {w : W}
  {c : G.Walk w w}
  {A : SimpleGraph V}
  {B' : Set (Sym2 V)}
  {a b : V}
-- given
  (hc : c.IsCycle)
  (h : ecc_DualCutModel A B' a b) :
-- imply
  faceCount c.toSubgraph.coe = 2 ∧ Nat.card ((A.deleteEdges B').deleteEdges {s(a, b)}).ConnectedComponent = 2 := by
-- proof
  apply StatMech.Lattice.ecc_cycle_dual_two_components c hc A B' h

/--
[ecc_dualModel_triangle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerComponentCount.lean)
-/
@[path]
private lemma ecc_dualModel_triangle_eq
  [Empty.Finite V]
  [DecidableEq V] :
-- imply
  ecc_DualCutModel (⊤ : SimpleGraph (Fin 3)) {s(0, 1)} 1 2 := by
-- proof
  apply StatMech.Lattice.ecc_dualModel_triangle

/--
[ecc_two_components_triangle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerComponentCount.lean)
-/
@[path]
private lemma ecc_two_components_triangle_eq
  [Empty.Finite V]
  [DecidableEq V] :
-- imply
  Nat.card (((⊤ : SimpleGraph (Fin 3)).deleteEdges {s(0, 1)}).deleteEdges {s(1, 2)}).ConnectedComponent = 2 := by
-- proof
  apply StatMech.Lattice.ecc_two_components_triangle


-- created on 2026-10-23
