/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/PairingsTheorems.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.NumberTheoryI.code.Pairings.Part2
import Mathlib.LinearAlgebra.BilinearForm.DualLattice
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.Algebra.Module.Lattice
open Submodule LinearMap Module


noncomputable section

section AuxDefs

variable {K : Type*} [Field K]

def directSumBilinForm {V₁ : Type*} [AddCommGroup V₁] [Module K V₁]
    {V₂ : Type*} [AddCommGroup V₂] [Module K V₂]
    (B₁ : V₁ →ₗ[K] V₁ →ₗ[K] K) (B₂ : V₂ →ₗ[K] V₂ →ₗ[K] K) :
    (V₁ × V₂) →ₗ[K] (V₁ × V₂) →ₗ[K] K :=
  LinearMap.mk₂ K
    (fun p q => B₁ p.1 q.1 + B₂ p.2 q.2)
    (by intros; simp [map_add, add_add_add_comm])
    (by intros; simp [map_smul, mul_add])
    (by intros; simp [map_add, add_add_add_comm])
    (by intros; simp [map_smul, mul_add])

end AuxDefs

def Submodule.localize {A : Type*} [CommRing A] {V : Type*} [AddCommGroup V] [Module A V]
    (S : Submonoid A) (M : Submodule A V) : Submodule A V where
  carrier := {v | ∃ s ∈ S, s • v ∈ M}
  add_mem' := by
    rintro a b ⟨s₁, hs₁, hsa⟩ ⟨s₂, hs₂, hsb⟩
    refine ⟨s₁ * s₂, S.mul_mem hs₁ hs₂, ?_⟩
    rw [smul_add, mul_smul, mul_smul, smul_comm s₁ s₂ a]
    exact M.add_mem (M.smul_mem s₂ hsa) (M.smul_mem s₁ hsb)
  zero_mem' := ⟨1, S.one_mem, by simp [M.zero_mem]⟩
  smul_mem' := by
    rintro c v ⟨s, hs, hsv⟩
    exact ⟨s, hs, by rw [smul_comm]; exact M.smul_mem _ hsv⟩

section Connection

variable
  {A : Type*} [CommRing A] [IsDomain A]
  {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
  {V : Type*} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]

noncomputable def dualBasis_inM_of_perfectPairing
    (B : M →ₗ[A] M →ₗ[A] A) [B.IsPerfPair] (b : Basis ι A M) :
    Basis ι A M :=
  b.dualBasis.map B.toPerfPair.symm

end Connection
end
