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
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryConnectivityTransfer.Part20
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable section

attribute [local instance] Classical.propDecidable


noncomputable def simpleGraph_sum_componentEquiv
    {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) :
    (G.sum H).ConnectedComponent ≃
      G.ConnectedComponent ⊕ H.ConnectedComponent := by
  let toSide : (G.sum H).ConnectedComponent ->
      G.ConnectedComponent ⊕ H.ConnectedComponent :=
    Quot.lift
      (fun z => match z with
        | Sum.inl v => Sum.inl (G.connectedComponentMk v)
        | Sum.inr w => Sum.inr (H.connectedComponentMk w))
      (by
        intro a b hab
        cases a with
        | inl a =>
            cases b with
            | inl b =>
                exact congrArg Sum.inl
                  (SimpleGraph.ConnectedComponent.sound
                    ((simpleGraph_sum_reachable_inl_iff).1 hab))
            | inr b => exact (simpleGraph_sum_not_reachable_inl_inr hab).elim
        | inr a =>
            cases b with
            | inl b => exact (simpleGraph_sum_not_reachable_inr_inl hab).elim
            | inr b =>
                exact congrArg Sum.inr
                  (SimpleGraph.ConnectedComponent.sound
                    ((simpleGraph_sum_reachable_inr_iff).1 hab)))
  let fromSide : G.ConnectedComponent ⊕ H.ConnectedComponent ->
      (G.sum H).ConnectedComponent
    | Sum.inl C => C.map SimpleGraph.Embedding.sumInl.toHom
    | Sum.inr C => C.map SimpleGraph.Embedding.sumInr.toHom
  refine
    { toFun := toSide
      invFun := fromSide
      left_inv := ?_
      right_inv := ?_ }
  · intro C
    refine SimpleGraph.ConnectedComponent.ind (G := G.sum H) ?_ C
    rintro (v | w) <;> rfl
  · rintro (C | C)
    · refine SimpleGraph.ConnectedComponent.ind (G := G) ?_ C
      intro v
      rfl
    · refine SimpleGraph.ConnectedComponent.ind (G := H) ?_ C
      intro w
      rfl

end
end StatMech.FrontierD
