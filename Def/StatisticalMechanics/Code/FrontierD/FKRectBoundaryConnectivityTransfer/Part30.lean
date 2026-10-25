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
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryConnectivityTransfer.Part27
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable section

attribute [local instance] Classical.propDecidable


def fkRectBoundarySeamGraph {W : Nat} (hW : 0 < W)
    (state : FKRectBoundaryState W)
    (eta : Bool × Fin W -> Bool) : SimpleGraph (Bool × Fin W) where
  Adj u v := state.Adj u v ∨
    ∃ a, eta a = true ∧
      (((fkRectBoundarySeamEdgeEndpoints hW a).1 = u ∧
          (fkRectBoundarySeamEdgeEndpoints hW a).2 = v) ∨
        ((fkRectBoundarySeamEdgeEndpoints hW a).1 = v ∧
          (fkRectBoundarySeamEdgeEndpoints hW a).2 = u))
  symm := by
    constructor
    rintro u v (hstate | hedge)
    · exact Or.inl hstate.symm
    · obtain ⟨a, ha, huv | huv⟩ := hedge
      · exact Or.inr ⟨a, ha, Or.inr ⟨huv.1, huv.2⟩⟩
      · exact Or.inr ⟨a, ha, Or.inl ⟨huv.1, huv.2⟩⟩
  loopless := ⟨by
    intro u huu
    rcases huu with hstate | hedge
    · exact state.loopless.irrefl u hstate
    · obtain ⟨a, _, huu | huu⟩ := hedge
      · exact fkRectBoundarySeamEdgeEndpoints_ne hW a
          (huu.1.trans huu.2.symm)
      · exact fkRectBoundarySeamEdgeEndpoints_ne hW a
          (huu.2.trans huu.1.symm).symm⟩


def fkRectBoundaryOpenSeamEdges {W : Nat} (hW : 0 < W)
    (eta : Bool × Fin W -> Bool) :
    List ((Bool × Fin W) × (Bool × Fin W)) :=
  (fkRectBoundaryOpenLayerIndices eta).map
    (fkRectBoundarySeamEdgeEndpoints hW)

end
end StatMech.FrontierD
