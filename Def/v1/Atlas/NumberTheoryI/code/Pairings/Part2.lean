/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Pairings.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Module
import Structure.v1.Atlas.NumberTheoryI.code.Pairings
open Submodule LinearMap


noncomputable section

section DualLattice

variable
  (A : Type*) [CommRing A] [IsDomain A]
  (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
  (V : Type*) [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]

def dualLattice (φ : V →ₗ[K] V →ₗ[K] K) (M : Submodule A V) : Submodule A V where
  carrier := {v : V | ∀ m ∈ M, φ v m ∈ (algebraMap A K).range}
  add_mem' {a b} (ha : ∀ m ∈ M, φ a m ∈ _) (hb : ∀ m ∈ M, φ b m ∈ _) m hm := by
    rw [map_add, add_apply]
    exact Subring.add_mem _ (ha m hm) (hb m hm)
  zero_mem' m _ := by
    rw [map_zero, zero_apply]
    exact Subring.zero_mem _
  smul_mem' c v (hv : ∀ m ∈ M, φ v m ∈ _) m hm := by
    have h1 : c • v = (algebraMap A K c) • v := by
      rw [Algebra.algebraMap_eq_smul_one, smul_assoc, one_smul]
    rw [h1, map_smul, smul_apply, smul_eq_mul]
    exact Subring.mul_mem _ ⟨c, rfl⟩ (hv m hm)

end DualLattice
end
