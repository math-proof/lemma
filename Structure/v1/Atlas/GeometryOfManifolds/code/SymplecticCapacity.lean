/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/SymplecticCapacity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.GeometryOfManifolds.code.SymplecticManifolds.Part3
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticManifolds
import Class.v1.Atlas.GeometryOfManifolds.code.SymplecticCapacity
set_option autoImplicit false

open DifferentialFormSpace


/-- A symplectic embedding $\varphi : (S_1, \omega_1) \hookrightarrow (S_2, \omega_2)$: a morphism satisfying $\varphi^*\omega_2 = \omega_1$. -/
structure SymplecticEmbedding
    {Ω₁ : ℕ → Type*} {VF₁ : Type*}
    {Ω₂ : ℕ → Type*} {VF₂ : Type*}
    [inst₁ : DifferentialFormSpace Ω₁ VF₁] [inst₂ : DifferentialFormSpace Ω₂ VF₂]
    (S₁ : SymplecticManifold Ω₁ VF₁) (S₂ : SymplecticManifold Ω₂ VF₂) where
  toMorphism : DFSMorphism Ω₁ VF₁ Ω₂ VF₂
  pullback_symplectic : toMorphism.pullback S₂.ω = S₁.ω


/-- A symplectic capacity $c$: a monotone invariant assigning $c(S) \in [0, \infty]$ to each symplectic manifold, satisfying $c(B^{2n}(r)) = c(Z^{2n}(r)) = \pi r^2$ (normalization) and $c(S_1) \le c(S_2)$ whenever $S_1$ embeds symplectically into $S_2$. -/
structure SymplecticCapacity
    (Ω : ℕ → Type*) (VF : Type*)
    [inst : DifferentialFormSpace Ω VF] where
  cap : SymplecticManifold Ω VF → NNReal
  monotonicity :
    ∀ (S₁ S₂ : SymplecticManifold Ω VF)
    (_φ : SymplecticEmbedding S₁ S₂),
    cap S₁ ≤ cap S₂
  normalization_ball :
    ∀ (S : SymplecticManifold Ω VF)
    [hBall : IsSymplecticBall S],
    cap S = symplCapacity hBall.radius
  normalization_cylinder :
    ∀ (S : SymplecticManifold Ω VF)
    [hCyl : IsSymplecticCylinder S],
    cap S = symplCapacity hCyl.radius

