/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4OuterLeafDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareFiniteDuality
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4OuterLeafDual.Part6
open Finset Set SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.BeffaraDC StatMech.Ising

noncomputable section

noncomputable def pfdOuterLeafComponentEquiv (P : PlanarZ2Subgraph)
    (K : SimpleGraph P.V) :
    (pfdOuterLeafWiredGraph P
      (pfdOuterLeafClosedEdges P K)).ConnectedComponent ≃
      (pfdClosedDual P K).ConnectedComponent := by
  let f : (pfdOuterLeafWiredGraph P
      (pfdOuterLeafClosedEdges P K)).ConnectedComponent →
      (pfdClosedDual P K).ConnectedComponent :=
    fun C => (pfdClosedDual P K).connectedComponentMk
      (pfdOuterLeafCollapse P C.out)
  apply Equiv.ofBijective f
  constructor
  · intro C D hCD
    change (pfdClosedDual P K).connectedComponentMk
      (pfdOuterLeafCollapse P C.out) =
        (pfdClosedDual P K).connectedComponentMk
          (pfdOuterLeafCollapse P D.out) at hCD
    have hleaf := (pfdOuterLeaf_reachable_iff_dual P K).mpr
      (ConnectedComponent.eq.mp hCD)
    rw [← C.out_eq, ← D.out_eq]
    exact ConnectedComponent.sound hleaf
  · intro D
    let x := pfdOuterLeafLift P D.out
    refine ⟨(pfdOuterLeafWiredGraph P
      (pfdOuterLeafClosedEdges P K)).connectedComponentMk x, ?_⟩
    dsimp only [f]
    rw [← D.out_eq]
    apply ConnectedComponent.sound
    have hout : (pfdOuterLeafWiredGraph P
        (pfdOuterLeafClosedEdges P K)).Reachable
        ((pfdOuterLeafWiredGraph P
          (pfdOuterLeafClosedEdges P K)).connectedComponentMk x).out x :=
      ConnectedComponent.exact
        ((pfdOuterLeafWiredGraph P
          (pfdOuterLeafClosedEdges P K)).connectedComponentMk x).out_eq
    have hdual := pfdOuterLeaf_collapse_reachable P K hout
    simpa only [x, pfdOuterLeafCollapse_lift] using hdual


end
end StatMech.FrontierD
