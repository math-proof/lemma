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
open SimpleGraph Set

set_option linter.unusedSectionVars false


namespace StatMech

namespace Lattice

variable {V : Type*} [Finite V] [DecidableEq V]


theorem tnse_connected_of_card_components_eq_one {G : SimpleGraph V}
    (hcard : Nat.card G.ConnectedComponent = 1) : G.Connected := by
  classical
  have hu := Nat.card_eq_one_iff_unique.mp hcard
  have hss : Subsingleton G.ConnectedComponent := hu.1
  obtain ⟨c⟩ := hu.2
  have hV : Nonempty V := c.exists_rep.elim fun v _ => ⟨v⟩
  rw [connected_iff]
  refine ⟨fun x y => ?_, hV⟩
  exact ConnectedComponent.exact (Subsingleton.elim (G.connectedComponentMk x)
    (G.connectedComponentMk y))


theorem tnse_connected_deleteEdge_of_nonbridge (A : SimpleGraph V) (hA : A.Connected) {a b : V}
    (he : s(a, b) ∈ A.edgeSet) (hr : (A.deleteEdges {s(a, b)}).Reachable a b) :
    (A.deleteEdges {s(a, b)}).Connected := by
  have hcard : Nat.card (A.deleteEdges {s(a, b)}).ConnectedComponent = 1 := by
    rw [ecc_deleteEdge_card_nonbridge A he hr, card_components_eq_one_of_connected hA]
  exact tnse_connected_of_card_components_eq_one hcard


end Lattice
end StatMech
