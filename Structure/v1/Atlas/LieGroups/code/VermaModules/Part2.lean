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
import Def.v1.Atlas.LieGroups.code.VermaModules


noncomputable section

universe u_mod

variable (R : Type*) [CommRing R]

variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]

variable {R 𝔤}

namespace TriangularDecomposition

variable (Δ : TriangularDecomposition R 𝔤)

structure IsHighestWeightModule
    (Δ : TriangularDecomposition R 𝔤)
    (M : Type u_mod) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (wt : Δ.𝔥 →ₗ[R] R) where
  highestWeightVec : M
  hwv_ne_zero : highestWeightVec ≠ 0
  cartan_action : ∀ (h : Δ.𝔥), ⁅(h : 𝔤), highestWeightVec⁆ = wt h • highestWeightVec
  npos_action : ∀ (e : Δ.𝔫_pos), ⁅(e : 𝔤), highestWeightVec⁆ = 0
  generates : LieSubmodule.lieSpan R 𝔤 {highestWeightVec} = ⊤

structure IsVermaModule
    (Δ : TriangularDecomposition R 𝔤)
    (M : Type u_mod) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (wt : Δ.𝔥 →ₗ[R] R)
    extends IsHighestWeightModule Δ M wt where
  universal_map :
    ∀ (V : Type u_mod) [AddCommGroup V] [Module R V] [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
      (v : V),
      (∀ (h : Δ.𝔥), ⁅(h : 𝔤), v⁆ = wt h • v) →
      (∀ (e : Δ.𝔫_pos), ⁅(e : 𝔤), v⁆ = 0) →
      ∃ (η : M →ₗ⁅R, 𝔤⁆ V), η highestWeightVec = v
  universal_unique :
    ∀ (V : Type u_mod) [AddCommGroup V] [Module R V] [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
      (η₁ η₂ : M →ₗ⁅R, 𝔤⁆ V),
      η₁ highestWeightVec = η₂ highestWeightVec → η₁ = η₂

end TriangularDecomposition
end
