/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerComponentCount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanEulerSeparation.Part2
import Def.StatisticalMechanics.Code.Lattice.EulerComponentCount
open SimpleGraph Set


set_option linter.unusedSectionVars false


namespace StatMech

namespace Lattice

variable {V : Type*} [Finite V] [DecidableEq V]


theorem ecc_two_components_of_dualModel (A : SimpleGraph V) (B' : Set (Sym2 V)) {a b : V}
    (h : ecc_DualCutModel A B' a b) :
    Nat.card ((A.deleteEdges B').deleteEdges {s(a, b)}).ConnectedComponent = 2 := by
  obtain ⟨hconn, he, hbridge⟩ := h
  exact ecc_two_components_tree_plus_bridge A B' hconn he hbridge


theorem ecc_cycle_dual_two_components {W : Type*} [Finite W] [DecidableEq W]
    {G : SimpleGraph W} {w : W}
    (c : G.Walk w w) (hc : c.IsCycle)
    (A : SimpleGraph V) (B' : Set (Sym2 V)) {a b : V} (h : ecc_DualCutModel A B' a b) :
    faceCount c.toSubgraph.coe = 2 ∧
      Nat.card ((A.deleteEdges B').deleteEdges {s(a, b)}).ConnectedComponent = 2 :=
  ⟨jes_cycle_faceCount_two c hc, ecc_two_components_of_dualModel A B' h⟩


theorem ecc_dualModel_triangle :
    ecc_DualCutModel (⊤ : SimpleGraph (Fin 3)) {s(0, 1)} 1 2 :=
  ⟨by decide, by decide, by decide⟩


theorem ecc_two_components_triangle :
    Nat.card (((⊤ : SimpleGraph (Fin 3)).deleteEdges {s(0, 1)}).deleteEdges
      {s(1, 2)}).ConnectedComponent = 2 :=
  ecc_two_components_of_dualModel (⊤ : SimpleGraph (Fin 3)) {s(0, 1)} ecc_dualModel_triangle


end Lattice
end StatMech
