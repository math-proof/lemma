/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TreeNoSepEuler.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.EulerComponentCount.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces.Part3
import Def.StatisticalMechanics.Code.Lattice.TreeNoSepEuler.Part3
open SimpleGraph Set

set_option linter.unusedSectionVars false


namespace StatMech

namespace Lattice

variable {V : Type*} [Finite V] [DecidableEq V]


@[simp] theorem tnse_allNonBridge_nil (A : SimpleGraph V) : tnse_AllNonBridge A [] := trivial

theorem tnse_allNonBridge_cons {A : SimpleGraph V} {e : Sym2 V} {L : List (Sym2 V)}
    (hhead : tnse_IsNonBridgeEdge (tnse_deleteList A L) e) (htail : tnse_AllNonBridge A L) :
    tnse_AllNonBridge A (e :: L) := ⟨hhead, htail⟩


theorem tnse_connected_deleteList_of_allNonBridge (A : SimpleGraph V) (hA : A.Connected)
    {L : List (Sym2 V)} (hnb : tnse_AllNonBridge A L) :
    (tnse_deleteList A L).Connected := by
  induction L with
  | nil => simpa using hA
  | cons e L ih =>
    obtain ⟨hhead, htail⟩ := hnb
    rw [tnse_deleteList_cons]
    exact tnse_connected_deleteEdge_of_isNonBridge (tnse_deleteList A L) (ih htail) hhead


theorem tnse_reachable_of_detour (A : SimpleGraph V) {a b a' b' : V}
    (h1 : A.Adj a a') (h2 : A.Adj a' b') (h3 : A.Adj b' b)
    (hne1 : s(a, a') ≠ s(a, b)) (hne2 : s(a', b') ≠ s(a, b)) (hne3 : s(b', b) ≠ s(a, b)) :
    (A.deleteEdges {s(a, b)}).Reachable a b := by
  have d1 : (A.deleteEdges {s(a, b)}).Adj a a' :=
    (SimpleGraph.deleteEdges_adj).mpr ⟨h1, by simpa using hne1⟩
  have d2 : (A.deleteEdges {s(a, b)}).Adj a' b' :=
    (SimpleGraph.deleteEdges_adj).mpr ⟨h2, by simpa using hne2⟩
  have d3 : (A.deleteEdges {s(a, b)}).Adj b' b :=
    (SimpleGraph.deleteEdges_adj).mpr ⟨h3, by simpa using hne3⟩
  exact (Walk.cons d1 (Walk.cons d2 (Walk.cons d3 Walk.nil))).reachable


theorem tnse_grid_edge_nonbridge_of_detour (A : SimpleGraph V) {a b a' b' : V}
    (hab : s(a, b) ∈ A.edgeSet)
    (h1 : A.Adj a a') (h2 : A.Adj a' b') (h3 : A.Adj b' b)
    (hne1 : s(a, a') ≠ s(a, b)) (hne2 : s(a', b') ≠ s(a, b)) (hne3 : s(b', b) ≠ s(a, b)) :
    tnse_IsNonBridgeEdge A s(a, b) :=
  ⟨a, b, rfl, hab, tnse_reachable_of_detour A h1 h2 h3 hne1 hne2 hne3⟩


end Lattice
end StatMech
