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
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryConnectivityTransfer.Part21
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable section

attribute [local instance] Classical.propDecidable


noncomputable def fkRectBoundaryInitialComponentEquiv (W : Nat) :
    (fkRectBoundaryInitialState W).ConnectedComponent ≃ Fin W := by
  let f : Fin W -> (fkRectBoundaryInitialState W).ConnectedComponent :=
    fun x => (fkRectBoundaryInitialState W).connectedComponentMk (false, x)
  exact (Equiv.ofBijective f ⟨by
    intro x y hxy
    exact (fkRectBoundaryInitialState_reachable_iff W (false, x) (false, y)).1
      (SimpleGraph.ConnectedComponent.exact hxy), by
    intro C
    refine SimpleGraph.ConnectedComponent.ind (G := fkRectBoundaryInitialState W)
      ?_ C
    rintro ⟨b, x⟩
    refine ⟨x, ?_⟩
    apply SimpleGraph.ConnectedComponent.sound
    exact (fkRectBoundaryInitialState_reachable_iff W (false, x) (b, x)).2 rfl⟩).symm

end
end StatMech.FrontierD
