/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/HyperbolicCancellation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.Tactic.LinearCombination
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.BilinearForm
set_option maxHeartbeats 0


namespace Garrett

variable {k : Type*} [Field k]


/-- The orthogonal direct sum of two bilinear forms `B₁` on `V₁` and `B₂` on `V₂`,
defined on the product space by `(p, q) ↦ B₁ p.1 q.1 + B₂ p.2 q.2`. -/
noncomputable def BilinForm.orthogonalSum {V₁ V₂ : Type*} [AddCommGroup V₁] [Module k V₁]
    [AddCommGroup V₂] [Module k V₂]
    (B₁ : LinearMap.BilinForm k V₁) (B₂ : LinearMap.BilinForm k V₂) :
    LinearMap.BilinForm k (V₁ × V₂) :=
  LinearMap.mk₂ k (fun p q => B₁ p.1 q.1 + B₂ p.2 q.2)
    (by intro x y z; simp [map_add, LinearMap.add_apply]; ring)
    (by intro c x y; simp [map_smul, LinearMap.smul_apply]; ring)
    (by intro x y z; simp [map_add]; ring)
    (by intro c x y; simp; ring)

/-- A bilinear form is nondegenerate (in the orthogonal-complement sense) when
the orthogonal complement of the whole space is trivial. -/
def BilinForm.IsNondegenerate' {V : Type*} [AddCommGroup V] [Module k V]
    (B : LinearMap.BilinForm k V) : Prop :=
  LinearMap.BilinForm.orthogonal B ⊤ = ⊥

/-- A bilinear form `B` is hyperbolic if it is nondegenerate and admits a
Lagrangian subspace `W` (a totally isotropic subspace equal to its own orthogonal
complement). -/
def BilinForm.IsHyperbolic {V : Type*} [AddCommGroup V] [Module k V]
    (B : LinearMap.BilinForm k V) : Prop :=
  ∃ (W : Submodule k V),
    (∀ w₁ ∈ W, ∀ w₂ ∈ W, B w₁ w₂ = 0) ∧
    LinearMap.BilinForm.orthogonal B W = W ∧
    BilinForm.IsNondegenerate' B

/-- A linear equivalence `φ : V₁ ≃ₗ V₂` is an isometry of formed spaces if it
preserves the corresponding bilinear forms `B₁` and `B₂`. -/
def IsFormedSpaceIsometry {V₁ V₂ : Type*} [AddCommGroup V₁] [Module k V₁]
    [AddCommGroup V₂] [Module k V₂]
    (B₁ : LinearMap.BilinForm k V₁) (B₂ : LinearMap.BilinForm k V₂)
    (φ : V₁ ≃ₗ[k] V₂) : Prop :=
  ∀ v w : V₁, B₂ (φ v) (φ w) = B₁ v w

/-- Two formed spaces `(V₁, B₁)` and `(V₂, B₂)` are isometric if there exists a
linear equivalence between them preserving the bilinear forms. -/
def FormedSpacesIsometric {V₁ V₂ : Type*} [AddCommGroup V₁] [Module k V₁]
    [AddCommGroup V₂] [Module k V₂]
    (B₁ : LinearMap.BilinForm k V₁) (B₂ : LinearMap.BilinForm k V₂) : Prop :=
  ∃ φ : V₁ ≃ₗ[k] V₂, IsFormedSpaceIsometry B₁ B₂ φ

/-- The diagonal subspace `{(v, v) | v ∈ V}` of `V × V`. -/
def diagonal (V : Type*) [AddCommGroup V] [Module k V] : Submodule k (V × V) where
  carrier := {p | p.1 = p.2}
  add_mem' := by intro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ (ha : a₁ = a₂) (hb : b₁ = b₂); simp [ha, hb]
  zero_mem' := rfl
  smul_mem' := by intro c ⟨a₁, a₂⟩ (ha : a₁ = a₂); simp [ha]

/-- A rearrangement linear equivalence permuting the four factors of
`(X × Y) × (U × U)` into `(U × X) × (U × Y)`. -/
noncomputable def rearrangeEquiv : ((X × Y) × (U × U)) ≃ₗ[k] ((U × X) × (U × Y)) :=
  (show ((X × Y) × (U × U)) ≃ₗ[k] ((U × X) × (U × Y)) from
  { toFun := fun p => ((p.2.1, p.1.1), (p.2.2, p.1.2))
    invFun := fun p => ((p.1.2, p.2.2), (p.1.1, p.2.1))
    left_inv := by intro p; ext <;> rfl
    right_inv := by intro p; ext <;> rfl
    map_add' := by intro ⟨⟨_, _⟩, ⟨_, _⟩⟩ ⟨⟨_, _⟩, ⟨_, _⟩⟩; rfl
    map_smul' := by intro _ ⟨⟨_, _⟩, ⟨_, _⟩⟩; rfl })


end Garrett
