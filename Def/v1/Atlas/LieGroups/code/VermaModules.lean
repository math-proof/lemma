/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/VermaModules.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Lie.Basic
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Lie.Subalgebra
public import Mathlib.Algebra.Lie.Submodule
public import Mathlib.Algebra.Lie.Quotient
public import Mathlib.Algebra.Lie.UniversalEnveloping
public import Mathlib.Algebra.Lie.Weights.Basic
public import Mathlib.Algebra.Lie.Semisimple.Basic
public import Mathlib.Algebra.Lie.CartanSubalgebra
public import Mathlib.Order.Atoms
public import Mathlib.RingTheory.Congruence.Defs
public import Structure.v1.Atlas.LieGroups.code.VermaModules

@[expose] public section

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
