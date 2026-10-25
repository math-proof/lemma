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
import Structure.v1.Atlas.LieGroups.code.VermaModules


noncomputable section

universe u_mod

variable (R : Type*) [CommRing R]

variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]

variable {R 𝔤}

namespace TriangularDecomposition

variable (Δ : TriangularDecomposition R 𝔤)

def 𝔟 : LieSubalgebra R 𝔤 := Δ.𝔥 ⊔ Δ.𝔫_pos

def weightSubspace
    (M : Type u_mod) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (μ : Δ.𝔥 →ₗ[R] R) : Submodule R M where
  carrier := {m : M | ∀ h : Δ.𝔥, ⁅(h : 𝔤), m⁆ = μ h • m}
  add_mem' {a b} ha hb h := by rw [lie_add, ha h, hb h, smul_add]
  zero_mem' h := by rw [lie_zero, smul_zero]
  smul_mem' c _ hm h := by rw [LieModule.lie_smul, hm h, smul_comm]

end TriangularDecomposition
end
