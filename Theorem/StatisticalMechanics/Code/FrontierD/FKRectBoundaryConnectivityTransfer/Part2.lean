/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusRandomCluster.Part5
import Theorem.StatisticalMechanics.Code.Foundations.FiniteNonnegativeMatrixRate.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
import Def.StatisticalMechanics.Code.FrontierD.FKRectBoundaryConnectivityTransfer.Part2
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable section

attribute [local instance] Classical.propDecidable


theorem finite_component_count_eq_closed_add_boundary
    {V B : Type*} [Fintype V] [Fintype B] [DecidableEq V] [DecidableEq B]
    (G : SimpleGraph V) (embed : B -> V) :
    Fintype.card G.ConnectedComponent =
      (Finset.univ.filter fun C : G.ConnectedComponent =>
        ∀ u : B, G.connectedComponentMk (embed u) ≠ C).card +
      Fintype.card
        (finiteBoundaryConnectivityGraph G embed).ConnectedComponent := by
  classical
  let p : G.ConnectedComponent -> Prop := fun C =>
    ∃ u : B, G.connectedComponentMk (embed u) = C
  have hmeet : Fintype.card
      (finiteBoundaryConnectivityGraph G embed).ConnectedComponent =
      Fintype.card {C : G.ConnectedComponent // p C} :=
    Fintype.card_congr (finiteBoundaryComponentEquiv G embed)
  have hclosed :
      (Finset.univ.filter fun C : G.ConnectedComponent =>
        ∀ u : B, G.connectedComponentMk (embed u) ≠ C).card =
      Fintype.card {C : G.ConnectedComponent // ¬p C} := by
    rw [Fintype.card_subtype]
    congr 1
    ext C
    simp [p]
  rw [hclosed, hmeet, Fintype.card_subtype_compl]
  exact (Nat.sub_add_cancel (Fintype.card_subtype_le p)).symm


end
end StatMech.FrontierD
