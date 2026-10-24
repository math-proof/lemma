/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/AffineWeylGroupConstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.Buildings.code.Reflection.AffineWeylGroups

open scoped InnerProductSpace
open Set

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Full data for the affine Weyl group $W_a = W ⋉ Λ(\check Φ)$ in an inner product
space $E$: a finite reduced root system, the coroot map $\check α = (2/⟨α,α⟩) α$, the
coroot lattice, crystallographic integrality, stability of roots under $W$, and
integrality of coroot-lattice pairings with roots. -/
structure AffineWeylGroupFullData (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] extends AffineWeylGroupData E where
  roots_finite : Set.Finite roots
  coroot : E → E
  coroot_def : ∀ α ∈ roots, coroot α = (2 / ⟪α, α⟫_ℝ) • α
  coroot_mem_lattice : ∀ α ∈ roots, coroot α ∈ corootLattice
  crystallographic : ∀ α ∈ roots, ∀ β ∈ roots,
    ∃ n : ℤ, ⟪coroot α, β⟫_ℝ = ↑n
  weylGroup_stable_roots : ∀ w ∈ weylGroup, ∀ α ∈ roots,
    (w : E ≃ₗᵢ[ℝ] E) α ∈ roots
  corootLattice_int : ∀ α ∈ roots, ∀ v ∈ corootLattice,
    ∃ m : ℤ, ⟪v, α⟫_ℝ = ↑m

namespace AffineWeylGroupFullData

variable (d : AffineWeylGroupFullData E)

/-- Shorthand for the underlying affine hyperplane arrangement of the affine Weyl data. -/
def affineArr : HyperplaneArrangement E :=
  d.toAffineWeylGroupData.affineArrangement

/-- Formula for the affine reflection across $H_{α,k}$:
$s_{α,k}(v) = v - (⟨α,v⟩ - k) \check α$. -/
def affineReflFun (α : E) (k : ℤ) (v : E) : E :=
  v - (⟪α, v⟫_ℝ - ↑k) • d.coroot α

/-- Formula for the linear reflection through the hyperplane perpendicular to $α$:
$s_α(v) = v - ⟨α,v⟩ \check α$. -/
def linearReflFun (α : E) (v : E) : E :=
  v - ⟪α, v⟫_ℝ • d.coroot α
