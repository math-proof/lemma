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
import Def.StatisticalMechanics.Code.FrontierD.FKRectBoundaryConnectivityTransfer.Part12
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable section

attribute [local instance] Classical.propDecidable


theorem fkRectBoundaryEmptyLayer_new_reachable_iff
    {W : Nat} (hW : 0 < W) (evenRow : Bool)
    (state : FKRectBoundaryState W) (x : Fin W) (v : FKRectLayerVertex W) :
    (fkRectBoundaryLayerGraph hW evenRow state
      fkRectBoundaryEmptyLayer).Reachable
      (fkRectLayerNewRole, x) v ↔ v = (fkRectLayerNewRole, x) := by
  have hisolated :
      (fkRectBoundaryLayerGraph hW evenRow state
        fkRectBoundaryEmptyLayer).neighborSet (fkRectLayerNewRole, x) = ∅ := by
    ext w
    simp only [SimpleGraph.mem_neighborSet, Set.mem_empty_iff_false, iff_false]
    intro hadj
    rcases hadj with hstate | hedge
    · obtain ⟨u, z, _, hu, _⟩ := hstate
      rcases u with ⟨b, y⟩
      cases b <;> simp [fkRectLayerInputEmbed, fkRectLayerInitialRole,
        fkRectLayerOldRole, fkRectLayerNewRole] at hu
    · obtain ⟨a, ha, _⟩ := hedge
      simp [fkRectBoundaryEmptyLayer] at ha
  constructor
  · intro hreach
    by_contra hne
    exact (SimpleGraph.not_reachable_of_neighborSet_left_eq_empty (Ne.symm hne) hisolated)
      hreach
  · rintro rfl
    exact SimpleGraph.Reachable.refl _

theorem fkRectBoundaryEmptyLayer_input_reachable_iff
    {W : Nat} (hW : 0 < W) (evenRow : Bool)
    (state : FKRectBoundaryState W) (u v : Bool × Fin W) :
    (fkRectBoundaryLayerGraph hW evenRow state
      fkRectBoundaryEmptyLayer).Reachable
        (fkRectLayerInputEmbed u) (fkRectLayerInputEmbed v) ↔
      state.Reachable u v := by
  let collapseHom :
      fkRectBoundaryLayerGraph hW evenRow state fkRectBoundaryEmptyLayer →g
        state :=
    { toFun := fkRectLayerCollapse
      map_rel' := by
        intro a b hab
        rcases hab with hstate | hedge
        · obtain ⟨x, y, hxy, rfl, rfl⟩ := hstate
          simpa using hxy
        · obtain ⟨x, hx, _⟩ := hedge
          simp [fkRectBoundaryEmptyLayer] at hx }
  let inputHom : state →g
      fkRectBoundaryLayerGraph hW evenRow state fkRectBoundaryEmptyLayer :=
    { toFun := fkRectLayerInputEmbed
      map_rel' := by
        intro a b hab
        exact Or.inl ⟨a, b, hab, rfl, rfl⟩ }
  constructor
  · intro h
    simpa [collapseHom] using h.map collapseHom
  · intro h
    exact h.map inputHom


end
end StatMech.FrontierD
