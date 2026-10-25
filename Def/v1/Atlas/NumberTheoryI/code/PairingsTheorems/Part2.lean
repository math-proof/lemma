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
import Structure.v1.Atlas.NumberTheoryI.code.PairingsTheorems
open Submodule LinearMap Module


noncomputable section

section DirectSumDualLattice

def BilinForm.dualSubmoduleLoc
    {A : Type*} [CommRing A]
    {K : Type*} [Field K] [Algebra A K]
    {V : Type*} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
    (B : V →ₗ[K] V →ₗ[K] K) (S : Submonoid A) (M : Submodule A V) :
    Submodule A V where
  carrier := {v | ∀ y ∈ M, ∃ s ∈ S, s • (B v y) ∈ (1 : Submodule A K)}
  add_mem' := by
    intro a b ha hb y hy
    obtain ⟨s, hs, hs'⟩ := ha y hy
    obtain ⟨t, ht, ht'⟩ := hb y hy
    refine ⟨s * t, S.mul_mem hs ht, ?_⟩
    have key : (s * t) • (B (a + b) y) = t • (s • (B a y)) + s • (t • (B b y)) := by
      simp only [map_add, LinearMap.add_apply]
      rw [smul_add, mul_smul, mul_smul, smul_comm s t]
    rw [key]
    exact add_mem (Submodule.smul_mem _ t hs') (Submodule.smul_mem _ s ht')
  zero_mem' := by
    intro y _
    exact ⟨1, S.one_mem, by simp⟩
  smul_mem' := by
    intro c v hv y hy
    obtain ⟨s, hs, hs'⟩ := hv y hy
    refine ⟨s, hs, ?_⟩
    have key : s • (B (c • v) y) = c • (s • (B v y)) := by
      simp only [Algebra.smul_def, map_smul_of_tower, LinearMap.smul_apply]
      ring
    rw [key]
    exact Submodule.smul_mem _ c hs'

end DirectSumDualLattice
end
