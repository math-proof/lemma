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
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryConnectivityTransfer
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable section

attribute [local instance] Classical.propDecidable


noncomputable def finiteBoundaryComponentEquiv
    {V B : Type*} (G : SimpleGraph V) (embed : B -> V) :
    (finiteBoundaryConnectivityGraph G embed).ConnectedComponent ≃
      {C : G.ConnectedComponent //
        ∃ u : B, G.connectedComponentMk (embed u) = C} := by
  let K := finiteBoundaryConnectivityGraph G embed
  let toAmbient : K.ConnectedComponent -> G.ConnectedComponent :=
    Quot.lift (fun u : B => G.connectedComponentMk (embed u))
      (fun u v huv => SimpleGraph.ConnectedComponent.sound
        ((finiteBoundaryConnectivityGraph_reachable_iff G embed u v).1 huv))
  refine
    { toFun := fun C => ⟨toAmbient C, ?_⟩
      invFun := fun C => K.connectedComponentMk (Classical.choose C.2)
      left_inv := ?_
      right_inv := ?_ }
  · refine SimpleGraph.ConnectedComponent.ind (G := K) (fun u => ?_) C
    exact ⟨u, rfl⟩
  · intro C
    refine SimpleGraph.ConnectedComponent.ind (G := K) (fun u => ?_) C
    apply SimpleGraph.ConnectedComponent.sound
    apply (finiteBoundaryConnectivityGraph_reachable_iff G embed _ _).2
    apply SimpleGraph.ConnectedComponent.exact
    exact Classical.choose_spec (show
      ∃ b : B, G.connectedComponentMk (embed b) =
        G.connectedComponentMk (embed u) from ⟨u, rfl⟩)
  · rintro ⟨C, hC⟩
    apply Subtype.ext
    dsimp only
    exact Classical.choose_spec hC


end
end StatMech.FrontierD
