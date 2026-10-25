/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/SymplecticManifolds.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.DifferentialForms.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.DifferentialForms
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticLinearAlgebra
import Def.v1.Atlas.GeometryOfManifolds.code.SymplecticLinearAlgebra.Part3
import Class.v1.Atlas.GeometryOfManifolds.code.SymplecticManifolds.Part2
set_option autoImplicit false

open DifferentialFormSpace


/-- Auxiliary setup for the graph $\Gamma_\varphi \subset M_1 \times M_2$ of a map
$\varphi : M_1 \to M_2$ between symplectic manifolds: projections $\pi_1, \pi_2$, an embedding
$\gamma : M_1 \to \Gamma_\varphi$, and the compatibility $\gamma^*\pi_1^* = \mathrm{id}$,
$\gamma^*\pi_2^* = \varphi^*$. -/
structure GraphSetup
    (Ω₁ : ℕ → Type*) (VF₁ : Type*)
    (Ω₂ : ℕ → Type*) (VF₂ : Type*)
    (Ω_P : ℕ → Type*) (VF_P : Type*)
    [inst₁ : DifferentialFormSpace Ω₁ VF₁]
    [inst₂ : DifferentialFormSpace Ω₂ VF₂]
    [inst_P : DifferentialFormSpace Ω_P VF_P]
    (S₁ : SymplecticManifold Ω₁ VF₁)
    (S₂ : SymplecticManifold Ω₂ VF₂) where
  π₁ : DFSMorphism Ω_P VF_P Ω₁ VF₁
  π₂ : DFSMorphism Ω_P VF_P Ω₂ VF₂
  φ : DFSMorphism Ω₁ VF₁ Ω₂ VF₂
  γ : DFSMorphism Ω₁ VF₁ Ω_P VF_P
  dimM₁ : ℕ
  dimM₂ : ℕ
  dim_eq : dimM₁ = dimM₂
  γ_π₁ : ∀ {p : ℕ} (α : Ω₁ p), γ.pullback (π₁.pullback α) = α
  γ_π₂ : ∀ {p : ℕ} (β : Ω₂ p), γ.pullback (π₂.pullback β) = φ.pullback β

