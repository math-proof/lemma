/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/WittCancellationDirectSum.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Projection
import Mathlib.Order.RelClasses
import Def.v1.Atlas.Buildings.code.GeometricAlgebra.WittCancellationDirectSum.Part2
set_option maxHeartbeats 2000000


namespace Garrett

variable {k : Type*} [Field k] [NeZero (2 : k)]


/-- Witt extension lemma: any isometry `φ : U ⊕ V ≃ U ⊕ W` can be modified to
an isometry `Ψ` of the same formed spaces that fixes the `U`-summand pointwise. -/
theorem first_component_zero
    {U : Type*} [AddCommGroup U] [Module k U] [FiniteDimensional k U]
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {W : Type*} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (B_U : LinearMap.BilinForm k U)
    (B_V : LinearMap.BilinForm k V)
    (B_W : LinearMap.BilinForm k W)
    (hU_nd : IsNondegenerate' B_U)
    (Ψ : (U × V) ≃ₗ[k] (U × W))
    (hΨ : IsFormedSpaceIso (orthogonalSumForm B_U B_V) (orthogonalSumForm B_U B_W) Ψ)
    (hΨ_U : ∀ u : U, Ψ (u, 0) = (u, 0))
    (v : V) : (Ψ (0, v)).1 = 0 := by


  have h_ortho : ∀ u : U, B_U u (Ψ (0, v)).1 = 0 := by
    intro u
    have key := hΨ (u, 0) (0, v)
    simp [orthogonalSumForm_apply] at key
    rw [hΨ_U] at key; simp at key; exact key

  have h_mem : (Ψ (0, v)).1 ∈ LinearMap.BilinForm.orthogonal B_U ⊤ := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]; intro x _; exact h_ortho x
  rw [hU_nd] at h_mem; exact h_mem


end Garrett
