/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.Algebra.Lie.CartanCriterion
import Mathlib.Algebra.Lie.Quotient
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Theorem.Algebra.Lie.LeviDecomposition.Part4
/-!
# Levi decomposition

This file proves Weyl's complete reducibility theorem and the Levi decomposition for
finite-dimensional Lie algebras over fields of characteristic zero.
-/


namespace LeviDecomposition

open LieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

def leviHomVanishing
    {K L M : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    (W : LieSubmodule K L M) : LieSubmodule K L (M →ₗ[K] W) where
  carrier := {f | ∀ w : W, f w = 0}
  zero_mem' w := rfl
  add_mem' {f g} hf hg w := by rw [LinearMap.add_apply, hf, hg, add_zero]
  smul_mem' a f hf w := by rw [LinearMap.smul_apply, hf, smul_zero]
  lie_mem := by
    intro x f hf w
    rw [LieHom.lie_apply]
    rw [hf, lie_zero]
    have hfw := hf (⟨⁅x, w.1⁆, W.lie_mem w.2⟩ : W)
    simpa using hfw

def leviHomScalarMaps
    {K L M : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    (W : LieSubmodule K L M) : LieSubmodule K L (M →ₗ[K] W) where
  carrier := {f | ∃ a : K, ∀ w : W, f w = a • w}
  zero_mem' := ⟨0, fun w ↦ by simp⟩
  add_mem' {f g} := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a + b, fun w ↦ ?_⟩
    rw [LinearMap.add_apply, ha, hb, add_smul]
  smul_mem' c f := by
    rintro ⟨a, ha⟩
    refine ⟨c * a, fun w ↦ ?_⟩
    rw [LinearMap.smul_apply, ha, mul_smul]
  lie_mem := by
    intro x f hf
    obtain ⟨a, ha⟩ := hf
    refine ⟨0, fun w ↦ ?_⟩
    rw [LieHom.lie_apply, ha, lie_smul]
    have haw := ha (⟨⁅x, w.1⁆, W.lie_mem w.2⟩ : W)
    rw [haw]
    have hxw : ⁅x, w⁆ = (⟨⁅x, w.1⁆, W.lie_mem w.2⟩ : W) := rfl
    rw [hxw, sub_self, zero_smul]

end LeviDecomposition
