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
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryConnectivityTransfer.Part6
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable section

attribute [local instance] Classical.propDecidable


def fkRectBoundaryLayerGraph {W : Nat} (hW : 0 < W)
    (evenRow : Bool) (state : FKRectBoundaryState W)
    (eta : Bool × Fin W -> Bool) : SimpleGraph (FKRectLayerVertex W) where
  Adj u v :=
    (∃ x y, state.Adj x y ∧ fkRectLayerInputEmbed x = u ∧
      fkRectLayerInputEmbed y = v) ∨
    ∃ a, eta a = true ∧
      (((fkRectLayerEdgeEndpoints hW evenRow a).1 = u ∧
          (fkRectLayerEdgeEndpoints hW evenRow a).2 = v) ∨
        ((fkRectLayerEdgeEndpoints hW evenRow a).1 = v ∧
          (fkRectLayerEdgeEndpoints hW evenRow a).2 = u))
  symm := by
    constructor
    rintro u v (hstate | hedge)
    · obtain ⟨x, y, hxy, rfl, rfl⟩ := hstate
      exact Or.inl ⟨y, x, hxy.symm, rfl, rfl⟩
    · obtain ⟨a, ha, huv | huv⟩ := hedge
      · exact Or.inr ⟨a, ha, Or.inr ⟨huv.1, huv.2⟩⟩
      · exact Or.inr ⟨a, ha, Or.inl ⟨huv.1, huv.2⟩⟩
  loopless := ⟨by
    intro u huu
    rcases huu with hstate | hedge
    · obtain ⟨x, y, hxy, hx, hy⟩ := hstate
      have hxy' : x = y := fkRectLayerInputEmbed_injective (hx.trans hy.symm)
      exact state.loopless.irrefl x (hxy' ▸ hxy)
    · obtain ⟨a, _, huu | huu⟩ := hedge
      · exact fkRectLayerEdgeEndpoints_ne hW evenRow a
          (huu.1.trans huu.2.symm)
      · exact fkRectLayerEdgeEndpoints_ne hW evenRow a
          (huu.2.trans huu.1.symm).symm⟩


def fkRectBoundaryLayerOutput {W : Nat} (hW : 0 < W)
    (evenRow : Bool) (state : FKRectBoundaryState W)
    (eta : Bool × Fin W -> Bool) : FKRectBoundaryState W where
  Adj u v := u ≠ v ∧
    (fkRectBoundaryLayerGraph hW evenRow state eta).Reachable
      (fkRectLayerOutputEmbed u) (fkRectLayerOutputEmbed v)
  symm := by
    constructor
    rintro u v ⟨huv, hreach⟩
    exact ⟨huv.symm, hreach.symm⟩
  loopless := ⟨by simp⟩

end
end StatMech.FrontierD
