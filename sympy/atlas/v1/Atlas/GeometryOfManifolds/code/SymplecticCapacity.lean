/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/SymplecticCapacity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.GeometryOfManifolds.code.SymplecticManifolds
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticManifolds

set_option autoImplicit false

open DifferentialFormSpace


/-- The symplectic capacity of a ball or cylinder of radius $r$, defined as $\pi r^2$. -/
noncomputable def symplCapacity (r : ℝ) : NNReal :=
  ⟨Real.pi * r ^ 2, mul_nonneg Real.pi_nonneg (sq_nonneg r)⟩


/-- Marker class identifying a symplectic manifold $S$ as the standard symplectic ball $B^{2n}(r)$ of radius $r > 0$. -/
class IsSymplecticBall {Ω : ℕ → Type*} {VF : Type*}
    [DifferentialFormSpace Ω VF] (S : SymplecticManifold Ω VF) where
  radius : ℝ
  halfDim : ℕ
  radius_pos : 0 < radius
  halfDim_pos : 0 < halfDim
  ω_exact : IsExact' VF S.ω
  capacity_val : NNReal
  capacity_eq : capacity_val = symplCapacity radius

/-- Marker class identifying a symplectic manifold $S$ as the standard symplectic cylinder $Z^{2n}(r) = B^2(r) \times \mathbb{R}^{2n-2}$. -/
class IsSymplecticCylinder {Ω : ℕ → Type*} {VF : Type*}
    [DifferentialFormSpace Ω VF] (S : SymplecticManifold Ω VF) where
  radius : ℝ
  halfDim : ℕ
  radius_pos : 0 < radius
  halfDim_pos : 0 < halfDim
  ω_exact : IsExact' VF S.ω
  capacity_val : NNReal
  capacity_eq : capacity_val = symplCapacity radius


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
