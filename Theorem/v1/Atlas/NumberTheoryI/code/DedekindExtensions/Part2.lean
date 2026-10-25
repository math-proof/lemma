/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DedekindExtensions.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.RingTheory.FractionalIdeal.Operations
import Mathlib.RingTheory.FractionalIdeal.Inverse
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.NumberTheory.NumberField.Basic
import Def.v1.Atlas.NumberTheoryI.code.Pairings.Part2
import Def.v1.Atlas.NumberTheoryI.code.DedekindExtensions.Part2
open Module


noncomputable section

section DualColonSubmodule

variable (A : Type*) [CommRing A] [IsDomain A]

variable (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]

theorem dual_symmetric_relation (M : Submodule A K) (f : Module.Dual A M) (m₁ m₂ : M) :
    (m₁ : K) * algebraMap A K (f m₂) = (m₂ : K) * algebraMap A K (f m₁) := by
  obtain ⟨a₁, b₁, hb₁, hm₁⟩ := IsFractionRing.div_surjective A (m₁ : K)
  obtain ⟨a₂, b₂, hb₂, hm₂⟩ := IsFractionRing.div_surjective A (m₂ : K)
  have hb₁' := map_ne_zero_of_mem_nonZeroDivisors _ (IsFractionRing.injective A K) hb₁
  have hb₂' := map_ne_zero_of_mem_nonZeroDivisors _ (IsFractionRing.injective A K) hb₂
  have key₁ : algebraMap A K b₁ * (m₁ : K) = algebraMap A K a₁ := by rw [← hm₁]; field_simp
  have key₂ : algebraMap A K b₂ * (m₂ : K) = algebraMap A K a₂ := by rw [← hm₂]; field_simp
  have hm₁_mem : algebraMap A K a₁ ∈ M := by
    rw [← key₁, ← Algebra.smul_def]; exact M.smul_mem b₁ m₁.2
  have hm₂_mem : algebraMap A K a₂ ∈ M := by
    rw [← key₂, ← Algebra.smul_def]; exact M.smul_mem b₂ m₂.2
  have eq₁ : f ⟨algebraMap A K a₁, hm₁_mem⟩ = b₁ * f m₁ := by
    have : (⟨algebraMap A K a₁, hm₁_mem⟩ : M) = b₁ • m₁ := by
      ext; simp [Algebra.smul_def, key₁]
    rw [this, map_smul, smul_eq_mul]
  have eq₂ : f ⟨algebraMap A K a₂, hm₂_mem⟩ = b₂ * f m₂ := by
    have : (⟨algebraMap A K a₂, hm₂_mem⟩ : M) = b₂ • m₂ := by
      ext; simp [Algebra.smul_def, key₂]
    rw [this, map_smul, smul_eq_mul]
  rw [show (m₁ : K) = algebraMap A K a₁ / algebraMap A K b₁ from hm₁.symm,
      show (m₂ : K) = algebraMap A K a₂ / algebraMap A K b₂ from hm₂.symm,
      div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_div_iff hb₁' hb₂']
  simp only [← map_mul]; congr 1
  calc a₁ * f m₂ * b₂
      = a₁ * (b₂ * f m₂) := by ring
    _ = a₁ * f ⟨algebraMap A K a₂, hm₂_mem⟩ := by rw [← eq₂]
    _ = f (a₁ • ⟨algebraMap A K a₂, hm₂_mem⟩) := by rw [map_smul, smul_eq_mul]
    _ = f (a₂ • ⟨algebraMap A K a₁, hm₁_mem⟩) := by
        congr 1; ext; simp [Algebra.smul_def, mul_comm]
    _ = a₂ * f ⟨algebraMap A K a₁, hm₁_mem⟩ := by rw [map_smul, smul_eq_mul]
    _ = a₂ * (b₁ * f m₁) := by rw [eq₁]
    _ = a₂ * f m₁ * b₁ := by ring

theorem dual_apply_via_element (M : Submodule A K) (f : Module.Dual A M)
    (m₀ : M) (hm₀ : (m₀ : K) ≠ 0) (m : M) :
    algebraMap A K (f m₀) * (m₀ : K)⁻¹ * (m : K) = algebraMap A K (f m) := by
  rw [← mul_right_inj' hm₀]
  calc (m₀ : K) * (algebraMap A K (f m₀) * (m₀ : K)⁻¹ * (m : K))
      = (m₀ : K) * (m₀ : K)⁻¹ * (algebraMap A K (f m₀) * (m : K)) := by ring
    _ = 1 * (algebraMap A K (f m₀) * (m : K)) := by rw [mul_inv_cancel₀ hm₀]
    _ = (m : K) * algebraMap A K (f m₀) := by ring
    _ = (m₀ : K) * algebraMap A K (f m) := dual_symmetric_relation A K M f m m₀

end DualColonSubmodule
end
