/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/VermaModules.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Algebra.Lie.Submodule
import Mathlib.Algebra.Lie.Quotient
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.Algebra.Lie.Weights.Basic
import Mathlib.Algebra.Lie.Semisimple.Basic
import Mathlib.Algebra.Lie.CartanSubalgebra
import Mathlib.Order.Atoms
import Mathlib.RingTheory.Congruence.Defs
import Def.v1.Atlas.LieGroups.code.VermaModules.Part3


noncomputable section

universe u_mod

variable (R : Type*) [CommRing R]

variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]

variable {R 𝔤}

namespace TriangularDecomposition

variable (Δ : TriangularDecomposition R 𝔤)

section UEASubalgHelpers

variable {R : Type*} [CommRing R]
  {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {M : Type*} [AddCommGroup M] [Module R M]
  [LieRingModule 𝔤 M] [LieModule R 𝔤 M]

structure PositiveRootData (Δ : TriangularDecomposition R 𝔤) where
  posRoots : Finset (Δ.𝔥 →ₗ[R] R)
  posRoots_ne_zero : ∀ α ∈ posRoots, α ≠ 0
  posRoots_pointed_cone : ∀ (α : Δ.𝔥 →ₗ[R] R), α ∈ posRoots →
    ∀ (n : ℤ), n < 0 →
    ¬ ∃ (c : (Δ.𝔥 →ₗ[R] R) → ℕ), n • α = ∑ β ∈ posRoots, (c β) • β
  corootPairing : (Δ.𝔥 →ₗ[R] R) → (Δ.𝔥 →ₗ[R] R) → R
  corootPairing_add_left : ∀ (μ ν α : Δ.𝔥 →ₗ[R] R),
    corootPairing (μ + ν) α = corootPairing μ α + corootPairing ν α
  corootPairing_nsmul_left : ∀ (n : ℕ) (μ α : Δ.𝔥 →ₗ[R] R),
    corootPairing (n • μ) α = n • corootPairing μ α
  corootPairing_self : ∀ α ∈ posRoots, corootPairing α α = 2
  negRootVec : ∀ α ∈ posRoots, ↥(Δ.𝔫_neg)
  negRootVec_weight : ∀ (α : Δ.𝔥 →ₗ[R] R) (hα : α ∈ posRoots) (h : Δ.𝔥),
    ⁅(↑h : 𝔤), (↑(negRootVec α hα) : 𝔤)⁆ = -(α h) • (↑(negRootVec α hα) : 𝔤)
  ι_negRootVec_ne_zero : ∀ (α : Δ.𝔥 →ₗ[R] R) (hα : α ∈ posRoots),
    UniversalEnvelopingAlgebra.ι R (negRootVec α hα) ≠ 0
  uea_nminus_noZeroDivisors : NoZeroDivisors (UniversalEnvelopingAlgebra R ↥(Δ.𝔫_neg))
  uea_nminus_nontrivial : Nontrivial (UniversalEnvelopingAlgebra R ↥(Δ.𝔫_neg))
  posRootVec : ∀ α ∈ posRoots, ↥(Δ.𝔫_pos)
  posRootVec_weight : ∀ (α : Δ.𝔥 →ₗ[R] R) (hα : α ∈ posRoots) (h : Δ.𝔥),
    ⁅(↑h : 𝔤), (↑(posRootVec α hα) : 𝔤)⁆ = (α h) • (↑(posRootVec α hα) : 𝔤)
  npos_span : ∀ (e : Δ.𝔫_pos), ∃ (c : ∀ α ∈ posRoots, R),
    (e : 𝔤) = ∑ x ∈ posRoots.attach, c x.1 x.2 • (↑(posRootVec x.1 x.2) : 𝔤)

end UEASubalgHelpers
end TriangularDecomposition
end
