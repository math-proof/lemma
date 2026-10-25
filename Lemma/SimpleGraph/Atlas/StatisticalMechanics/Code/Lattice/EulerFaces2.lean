import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
open SimpleGraph Set StatMech StatMech.Lattice


/--
[reachable_sup_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerFaces2.lean)
-/
@[path]
private lemma reachable_sup_edge_eq
  {G : SimpleGraph V}
  {a b x y : V} :
-- imply
  (G ⊔ edge a b).Reachable x y ↔ G.Reachable x y ∨ (G.Reachable x a ∧ G.Reachable b y) ∨ (G.Reachable x b ∧ G.Reachable a y) := by
-- proof
  apply StatMech.Lattice.reachable_sup_edge G a b x y

/--
[card_subtype_ne_add_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerFaces2.lean)
-/
@[path]
private lemma card_subtype_ne_add_one_eq
  [Empty.Finite α]
  {a : α} :
-- imply
  Nat.card {x : α // x ≠ a} + 1 = Nat.card α := by
-- proof
  apply StatMech.Lattice.card_subtype_ne_add_one a

/--
[card_components_sup_edge_of_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerFaces2.lean)
-/
@[path]
private lemma card_components_sup_edge_of_reachable_eq
  [Empty.Finite V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {a b : V}
-- given
  (hab : G.Reachable a b) :
-- imply
  Nat.card (G ⊔ edge a b).ConnectedComponent = Nat.card G.ConnectedComponent := by
-- proof
  apply StatMech.Lattice.card_components_sup_edge_of_reachable G a b hab

/--
[card_components_sup_edge_of_not_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerFaces2.lean)
-/
@[path]
private lemma card_components_sup_edge_of_not_reachable_eq
  [Empty.Finite V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {a b : V}
-- given
  (hab : ¬ G.Reachable a b) :
-- imply
  Nat.card (G ⊔ edge a b).ConnectedComponent + 1 = Nat.card G.ConnectedComponent := by
-- proof
  apply StatMech.Lattice.card_components_sup_edge_of_not_reachable G a b hab

/--
[deleteEdges_sup_edge_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerFaces2.lean)
-/
@[path]
private lemma deleteEdges_sup_edge_eq_eq
  [Empty.Finite V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {a b : V}
-- given
  (he : s(a, b) ∈ G.edgeSet) :
-- imply
  G = (G.deleteEdges {s(a, b)}) ⊔ edge a b := by
-- proof
  apply StatMech.Lattice.deleteEdges_sup_edge_eq G a b he

/--
[card_edgeSet_deleteEdges_add_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerFaces2.lean)
-/
@[path]
private lemma card_edgeSet_deleteEdges_add_one_eq
  [Empty.Finite V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {a b : V}
-- given
  (he : s(a, b) ∈ G.edgeSet) :
-- imply
  (G.deleteEdges {s(a, b)}).edgeSet.ncard + 1 = G.edgeSet.ncard := by
-- proof
  apply StatMech.Lattice.card_edgeSet_deleteEdges_add_one G a b he

/--
[card_edgeSet_sup_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerFaces2.lean)
-/
@[path]
private lemma card_edgeSet_sup_edge_eq
  [Empty.Finite V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {a b : V}
-- given
  (hne : a ≠ b)
  (hadj : ¬ G.Adj a b) :
-- imply
  (G ⊔ edge a b).edgeSet.ncard = G.edgeSet.ncard + 1 := by
-- proof
  apply StatMech.Lattice.card_edgeSet_sup_edge G hne hadj

/--
[card_components_bot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerFaces2.lean)
-/
@[path]
private lemma card_components_bot_eq
  [Empty.Finite V]
  [DecidableEq V] :
-- imply
  Nat.card (⊥ : SimpleGraph V).ConnectedComponent = Nat.card V := by
-- proof
  apply StatMech.Lattice.card_components_bot

/--
[card_le_edgeSet_add_components](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerFaces2.lean)
-/
@[path]
private lemma card_le_edgeSet_add_components_eq
  [Empty.Finite V]
  [DecidableEq V]
  {G : SimpleGraph V} :
-- imply
  Nat.card V ≤ G.edgeSet.ncard + Nat.card G.ConnectedComponent := by
-- proof
  apply StatMech.Lattice.card_le_edgeSet_add_components G

/--
[faceCount_sup_edge_of_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerFaces2.lean)
-/
@[path]
private lemma faceCount_sup_edge_of_reachable_eq
  [Empty.Finite V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {a b : V}
-- given
  (hne : a ≠ b)
  (hadj : ¬ G.Adj a b)
  (hab : G.Reachable a b) :
-- imply
  faceCount (G ⊔ edge a b) = faceCount G + 1 := by
-- proof
  apply StatMech.Lattice.faceCount_sup_edge_of_reachable G hne hadj hab

/--
[faceCount_sup_edge_of_not_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerFaces2.lean)
-/
@[path]
private lemma faceCount_sup_edge_of_not_reachable_eq
  [Empty.Finite V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {a b : V}
-- given
  (hne : a ≠ b)
  (hadj : ¬ G.Adj a b)
  (hab : ¬ G.Reachable a b) :
-- imply
  faceCount (G ⊔ edge a b) = faceCount G := by
-- proof
  apply StatMech.Lattice.faceCount_sup_edge_of_not_reachable G hne hadj hab

/--
[euler_relation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerFaces2.lean)
-/
@[path]
private lemma euler_relation_eq
  [Empty.Finite V]
  [DecidableEq V]
  {G : SimpleGraph V} :
-- imply
  Nat.card V + faceCount G = G.edgeSet.ncard + Nat.card G.ConnectedComponent + 1 := by
-- proof
  apply StatMech.Lattice.euler_relation G

/--
[euler_relation_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerFaces2.lean)
-/
@[path]
private lemma euler_relation_sub_eq
  [Empty.Finite V]
  [DecidableEq V]
  {G : SimpleGraph V} :
-- imply
  (Nat.card V : ℤ) - G.edgeSet.ncard + faceCount G = Nat.card G.ConnectedComponent + 1 := by
-- proof
  apply StatMech.Lattice.euler_relation_sub G

/--
[card_components_eq_one_of_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerFaces2.lean)
-/
@[path]
private lemma card_components_eq_one_of_connected_eq
  [Empty.Finite V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (hG : G.Connected) :
-- imply
  Nat.card G.ConnectedComponent = 1 := by
-- proof
  apply StatMech.Lattice.card_components_eq_one_of_connected hG

/--
[euler_connected_nat](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerFaces2.lean)
-/
@[path]
private lemma euler_connected_nat_eq
  [Empty.Finite V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (hG : G.Connected) :
-- imply
  Nat.card V + faceCount G = G.edgeSet.ncard + 2 := by
-- proof
  apply StatMech.Lattice.euler_connected_nat hG

/--
[euler_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerFaces2.lean)
-/
@[path]
private lemma euler_connected_eq
  [Empty.Finite V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (hG : G.Connected) :
-- imply
  (Nat.card V : ℤ) - G.edgeSet.ncard + faceCount G = 2 := by
-- proof
  apply StatMech.Lattice.euler_connected hG

/--
[nullity_eq_zero_of_isAcyclic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerFaces2.lean)
-/
@[path]
private lemma nullity_eq_zero_of_isAcyclic_eq
  [Empty.Finite V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (hG : G.IsAcyclic) :
-- imply
  nullity G = 0 := by
-- proof
  apply StatMech.Lattice.nullity_eq_zero_of_isAcyclic hG

/--
[faceCount_eq_one_of_isAcyclic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerFaces2.lean)
-/
@[path]
private lemma faceCount_eq_one_of_isAcyclic_eq
  [Empty.Finite V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (hG : G.IsAcyclic) :
-- imply
  faceCount G = 1 := by
-- proof
  apply StatMech.Lattice.faceCount_eq_one_of_isAcyclic hG

/--
[euler_tree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerFaces2.lean)
-/
@[path]
private lemma euler_tree_eq
  [Empty.Finite V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (hG : G.IsTree) :
-- imply
  (Nat.card V : ℤ) - G.edgeSet.ncard + faceCount G = 2 ∧ faceCount G = 1 := by
-- proof
  apply StatMech.Lattice.euler_tree hG

/--
[nullity_eq_cyclomaticNumber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerFaces2.lean)
-/
@[path]
private lemma nullity_eq_cyclomaticNumber_eq
  [Empty.Finite V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [Fintype V]
  [Fintype G.edgeSet]
-- given
  (hG : G.Connected) :
-- imply
  nullity G = cyclomaticNumber G := by
-- proof
  apply StatMech.Lattice.nullity_eq_cyclomaticNumber hG

/--
[faceCount_eq_cyclomaticNumber_add_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerFaces2.lean)
-/
@[path]
private lemma faceCount_eq_cyclomaticNumber_add_one_eq
  [Empty.Finite V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [Fintype V]
  [Fintype G.edgeSet]
-- given
  (hG : G.Connected) :
-- imply
  faceCount G = cyclomaticNumber G + 1 := by
-- proof
  apply StatMech.Lattice.faceCount_eq_cyclomaticNumber_add_one hG


-- created on 2026-10-23
