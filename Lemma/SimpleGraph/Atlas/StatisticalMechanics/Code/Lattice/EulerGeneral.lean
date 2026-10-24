import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Lattice.EulerGeneral
open SimpleGraph Set StatMech StatMech.Lattice


/--
[isBridge_iff_not_reachable_deleteEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerGeneral.lean)
-/
@[path]
private lemma isBridge_iff_not_reachable_deleteEdges_eq
  [Empty.Finite V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {a b : V}
-- given
  (he : s(a, b) ∈ G.edgeSet) :
-- imply
  G.IsBridge s(a, b) ↔ ¬ (G.deleteEdges {s(a, b)}).Reachable a b := by
-- proof
  apply StatMech.Lattice.isBridge_iff_not_reachable_deleteEdges G he

/--
[faceCount_deleteEdges_of_not_isBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerGeneral.lean)
-/
@[path]
private lemma faceCount_deleteEdges_of_not_isBridge_eq
  [Empty.Finite V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {a b : V}
-- given
  (he : s(a, b) ∈ G.edgeSet)
  (hr : (G.deleteEdges {s(a, b)}).Reachable a b) :
-- imply
  faceCount (G.deleteEdges {s(a, b)}) + 1 = faceCount G ∧ Nat.card (G.deleteEdges {s(a, b)}).ConnectedComponent = Nat.card G.ConnectedComponent := by
-- proof
  apply StatMech.Lattice.faceCount_deleteEdges_of_not_isBridge G he hr

/--
[faceCount_deleteEdges_of_isBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerGeneral.lean)
-/
@[path]
private lemma faceCount_deleteEdges_of_isBridge_eq
  [Empty.Finite V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {a b : V}
-- given
  (he : s(a, b) ∈ G.edgeSet)
  (hr : ¬ (G.deleteEdges {s(a, b)}).Reachable a b) :
-- imply
  faceCount (G.deleteEdges {s(a, b)}) = faceCount G ∧ Nat.card (G.deleteEdges {s(a, b)}).ConnectedComponent = Nat.card G.ConnectedComponent + 1 := by
-- proof
  apply StatMech.Lattice.faceCount_deleteEdges_of_isBridge G he hr

/--
[euler_general](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerGeneral.lean)
-/
@[path]
private lemma euler_general_eq
  [Empty.Finite V]
  [DecidableEq V]
  {G : SimpleGraph V} :
-- imply
  (Nat.card V : ℤ) - G.edgeSet.ncard + faceCount G = 1 + Nat.card G.ConnectedComponent := by
-- proof
  apply StatMech.Lattice.euler_general G

/--
[euler_general_nat](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerGeneral.lean)
-/
@[path]
private lemma euler_general_nat_eq
  [Empty.Finite V]
  [DecidableEq V]
  {G : SimpleGraph V} :
-- imply
  Nat.card V + faceCount G = G.edgeSet.ncard + Nat.card G.ConnectedComponent + 1 := by
-- proof
  apply StatMech.Lattice.euler_general_nat G

/--
[euler_general_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerGeneral.lean)
-/
@[path]
private lemma euler_general_connected_eq
  [Empty.Finite V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (hG : G.Connected) :
-- imply
  (Nat.card V : ℤ) - G.edgeSet.ncard + faceCount G = 2 := by
-- proof
  apply StatMech.Lattice.euler_general_connected hG

/--
[euler_general_disconnected_components](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerGeneral.lean)
-/
@[path]
private lemma euler_general_disconnected_components_eq
  [Empty.Finite V]
  [DecidableEq V]
  {G : SimpleGraph V} :
-- imply
  (Nat.card G.ConnectedComponent : ℤ) = (Nat.card V : ℤ) - G.edgeSet.ncard + faceCount G - 1 := by
-- proof
  apply StatMech.Lattice.euler_general_disconnected_components G

/--
[euler_general_eq_euler_relation_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerGeneral.lean)
-/
@[path]
private lemma euler_general_eq_euler_relation_sub_eq
  [Empty.Finite V]
  [DecidableEq V]
  {G : SimpleGraph V} :
-- imply
  (Nat.card V : ℤ) - G.edgeSet.ncard + faceCount G = Nat.card G.ConnectedComponent + 1 := by
-- proof
  apply StatMech.Lattice.euler_general_eq_euler_relation_sub G


-- created on 2026-10-23
