/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec12CoherentFiberSemicont.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.Algebra.Module.SpanRankOperations
import Mathlib.LinearAlgebra.Dimension.Constructions
set_option maxHeartbeats 400000

open scoped TensorProduct
open TensorProduct

universe u


/-- Fiber dimension of an `R`-module `M` at a prime `𝔭`: the dimension of the residue
field tensor product `κ(𝔭) ⊗_R M` over `κ(𝔭)`. -/
noncomputable def fiberDim {R : Type*} [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]
    (𝔭 : Ideal R) [𝔭.IsPrime] : ℕ :=
  Module.finrank 𝔭.ResidueField (𝔭.ResidueField ⊗[R] M)

/-- The base change `A ⊗_R (⊤ : Submodule R M) ≃ₗ[A] A ⊗_R M`: tensoring with the
inclusion of the top submodule is an isomorphism. -/
noncomputable def topEquivTensor (A R M : Type u) [CommRing R] [CommRing A]
    [Algebra R A] [AddCommGroup M] [Module R M] :
    A ⊗[R] (↥(⊤ : Submodule R M)) ≃ₗ[A] A ⊗[R] M :=
  LinearEquiv.ofLinear
    (AlgebraTensorModule.map (LinearMap.id : A →ₗ[A] A) Submodule.topEquiv.toLinearMap)
    (AlgebraTensorModule.map (LinearMap.id : A →ₗ[A] A) Submodule.topEquiv.symm.toLinearMap)
    (by apply AlgebraTensorModule.ext; intro a m; simp [Submodule.topEquiv])
    (by apply AlgebraTensorModule.ext; intro a m; simp [Submodule.topEquiv])

