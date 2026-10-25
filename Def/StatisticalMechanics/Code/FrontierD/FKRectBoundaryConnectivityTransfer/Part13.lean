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
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryConnectivityTransfer.Part11
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable section

attribute [local instance] Classical.propDecidable


noncomputable def fkRectBoundaryEmptyLayerClosedComponentEquiv
    {W : Nat} (hW : 0 < W) (evenRow : Bool)
    (state : FKRectBoundaryState W) :
    Fin W ≃
      {C : (fkRectBoundaryLayerGraph hW evenRow state
          fkRectBoundaryEmptyLayer).ConnectedComponent //
        ∀ u : Bool × Fin W,
          (fkRectBoundaryLayerGraph hW evenRow state
            fkRectBoundaryEmptyLayer).connectedComponentMk
              (fkRectLayerInputEmbed u) ≠ C} := by
  let G := fkRectBoundaryLayerGraph hW evenRow state fkRectBoundaryEmptyLayer
  let f : Fin W -> {C : G.ConnectedComponent //
      ∀ u : Bool × Fin W, G.connectedComponentMk
        (fkRectLayerInputEmbed u) ≠ C} := fun x =>
    ⟨G.connectedComponentMk (fkRectLayerNewRole, x), by
      intro u h
      have hreach : G.Reachable (fkRectLayerNewRole, x)
          (fkRectLayerInputEmbed u) :=
        SimpleGraph.ConnectedComponent.exact h.symm
      have heq := (fkRectBoundaryEmptyLayer_new_reachable_iff
        hW evenRow state x (fkRectLayerInputEmbed u)).1 hreach
      rcases u with ⟨b, y⟩
      cases b <;> simp [fkRectLayerInputEmbed, fkRectLayerInitialRole,
        fkRectLayerOldRole, fkRectLayerNewRole] at heq⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro x y hxy
    have hreach : G.Reachable (fkRectLayerNewRole, x)
        (fkRectLayerNewRole, y) :=
      SimpleGraph.ConnectedComponent.exact (congrArg Subtype.val hxy)
    have heq := (fkRectBoundaryEmptyLayer_new_reachable_iff
      hW evenRow state x (fkRectLayerNewRole, y)).1 hreach
    exact (congrArg Prod.snd heq).symm
  · rintro ⟨C, hC⟩
    obtain ⟨v, hv⟩ := Quot.exists_rep C
    have hval : v.1.val = 0 ∨ v.1.val = 1 ∨ v.1.val = 2 := by omega
    rcases hval with hzero | hone | htwo
    · exfalso
      apply hC (false, v.2)
      calc
        G.connectedComponentMk (fkRectLayerInputEmbed (false, v.2)) =
            G.connectedComponentMk v := by
              apply congrArg G.connectedComponentMk
              apply Prod.ext
              · apply Fin.ext
                simpa [fkRectLayerInputEmbed, fkRectLayerInitialRole] using hzero.symm
              · rfl
        _ = C := hv
    · exfalso
      apply hC (true, v.2)
      calc
        G.connectedComponentMk (fkRectLayerInputEmbed (true, v.2)) =
            G.connectedComponentMk v := by
              apply congrArg G.connectedComponentMk
              apply Prod.ext
              · apply Fin.ext
                simpa [fkRectLayerInputEmbed, fkRectLayerOldRole] using hone.symm
              · rfl
        _ = C := hv
    · refine ⟨v.2, ?_⟩
      apply Subtype.ext
      calc
        G.connectedComponentMk (fkRectLayerNewRole, v.2) =
            G.connectedComponentMk v := by
              apply congrArg G.connectedComponentMk
              apply Prod.ext
              · apply Fin.ext
                simpa [fkRectLayerNewRole] using htwo.symm
              · rfl
        _ = C := hv

end
end StatMech.FrontierD
