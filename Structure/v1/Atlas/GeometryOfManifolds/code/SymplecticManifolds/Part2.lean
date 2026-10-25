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
import Class.v1.Atlas.GeometryOfManifolds.code.SymplecticManifolds
set_option autoImplicit false

open DifferentialFormSpace


/-- A **symplectomorphism** (Definition 8): an invertible morphism of differential form spaces
$\varphi : (M_1, \omega_1) \to (M_2, \omega_2)$ satisfying $\varphi^* \omega_2 = \omega_1$. Encoded
with explicit two-sided inverse data at the level of pullbacks. -/
structure Symplectomorphism
    {Ω₁ : ℕ → Type*} {VF₁ : Type*}
    {Ω₂ : ℕ → Type*} {VF₂ : Type*}
    [inst₁ : DifferentialFormSpace Ω₁ VF₁] [inst₂ : DifferentialFormSpace Ω₂ VF₂]
    (S₁ : SymplecticManifold Ω₁ VF₁) (S₂ : SymplecticManifold Ω₂ VF₂) where
  toMorphism : DFSMorphism Ω₁ VF₁ Ω₂ VF₂
  invMorphism : DFSMorphism Ω₂ VF₂ Ω₁ VF₁
  left_inv : ∀ {p : ℕ} (β : Ω₂ p), invMorphism.pullback (toMorphism.pullback β) = β
  right_inv : ∀ {p : ℕ} (α : Ω₁ p), toMorphism.pullback (invMorphism.pullback α) = α
  pullback_symplectic : toMorphism.pullback S₂.ω = S₁.ω


/-- A submanifold $W \hookrightarrow M$ is **symplectic** when the pullback $i^*\omega$ remains
non-degenerate on $W$, i.e. $X \mapsto \iota_X (i^*\omega)$ is injective on $\mathfrak{X}(W)$. -/
structure IsSymplecticSubmanifold
    {Ω_M : ℕ → Type*} {VF_M : Type*}
    {Ω_W : ℕ → Type*} {VF_W : Type*}
    [inst_M : DifferentialFormSpace Ω_M VF_M]
    [inst_W : DifferentialFormSpace Ω_W VF_W]
    (S : SymplecticManifold Ω_M VF_M)
    (i : DFSMorphism Ω_W VF_W Ω_M VF_M) : Prop where
  restriction_nondegenerate :
    Function.Injective (fun (X : VF_W) => inst_W.ι X (i.pullback S.ω))

/-- A submanifold $L \hookrightarrow M$ is **Lagrangian** when $i^*\omega = 0$ and $\dim L =
\tfrac{1}{2}\dim M$, i.e. $L$ is isotropic of maximal dimension. -/
structure IsLagrangianSubmanifold
    {Ω_M : ℕ → Type*} {VF_M : Type*}
    {Ω_L : ℕ → Type*} {VF_L : Type*}
    [inst_M : DifferentialFormSpace Ω_M VF_M]
    [inst_L : DifferentialFormSpace Ω_L VF_L]
    (S : SymplecticManifold Ω_M VF_M)
    (i : DFSMorphism Ω_L VF_L Ω_M VF_M)
    (dimM : ℕ) (dimL : ℕ) : Prop where
  restriction_zero : i.pullback S.ω = 0
  half_dim : 2 * dimL = dimM


