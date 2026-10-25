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
import Theorem.v1.Atlas.Buildings.code.GeometricAlgebra.WittCancellationDirectSum.Part2
set_option maxHeartbeats 2000000


namespace Garrett

variable {k : Type*} [Field k] [NeZero (2 : k)]


/-- Extract a linear equivalence `V ≃ₗ W` from a `U`-fixing isometry `Ψ` of
`U ⊕ V` and `U ⊕ W`, by sending `v` to the second component of `Ψ (0, v)`. -/
noncomputable def extractEquiv
    {U : Type*} [AddCommGroup U] [Module k U] [FiniteDimensional k U]
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {W : Type*} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (B_U : LinearMap.BilinForm k U) (B_V : LinearMap.BilinForm k V)
    (B_W : LinearMap.BilinForm k W)
    (hU_nd : IsNondegenerate' B_U)
    (Ψ : (U × V) ≃ₗ[k] (U × W))
    (hΨ : IsFormedSpaceIso (orthogonalSumForm B_U B_V) (orthogonalSumForm B_U B_W) Ψ)
    (hΨ_U : ∀ u : U, Ψ (u, 0) = (u, 0)) :
    V ≃ₗ[k] W := by

  let f : V →ₗ[k] W :=
    { toFun := fun v => (Ψ (0, v)).2
      map_add' := fun v₁ v₂ => by
        have h := congr_arg Prod.snd (Ψ.map_add (0, v₁) (0, v₂))
        simp at h; exact h
      map_smul' := fun c v => by
        have h := congr_arg Prod.snd (Ψ.map_smul c (0, v))
        simp at h; exact h }


  have hf_inj : Function.Injective f := by
    intro v₁ v₂ hfv
    have hfst := first_component_zero B_U B_V B_W hU_nd Ψ hΨ hΨ_U
    have h1 : Ψ (0, v₁) = Ψ (0, v₂) := by
      ext
      · rw [hfst v₁, hfst v₂]
      · exact hfv
    exact Prod.ext_iff.mp (Ψ.injective h1) |>.2


  have hf_surj : Function.Surjective f := by
    have hdim : Module.finrank k V = Module.finrank k W := by
      have h1 : Module.finrank k (U × V) = Module.finrank k U + Module.finrank k V :=
        Module.finrank_prod
      have h2 : Module.finrank k (U × W) = Module.finrank k U + Module.finrank k W :=
        Module.finrank_prod
      linarith [LinearEquiv.finrank_eq Ψ]
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hf_inj
  exact LinearEquiv.ofBijective f ⟨hf_inj, hf_surj⟩

end Garrett
