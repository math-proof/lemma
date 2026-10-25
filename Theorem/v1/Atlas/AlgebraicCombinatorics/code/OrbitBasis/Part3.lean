/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/OrbitBasis.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.SMul
import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.GroupAction.Quotient
import Def.v1.Atlas.AlgebraicCombinatorics.code.OrbitBasis.Part3
set_option autoImplicit false


noncomputable section

open scoped Classical

open Finset Finsupp MulAction Function Module

namespace OrbitBasis

variable (G : Type*) [Group G] (α : Type*) [Fintype α] [DecidableEq α] [MulAction G α]

attribute [local instance] Finsupp.comapSMul Finsupp.comapMulAction
  Finsupp.comapDistribMulAction

variable {G α}

theorem orbitSum_apply (O : orbitRel.Quotient G α) (a : α) :
    orbitSum O a = if a ∈ orbitRel.Quotient.orbit O then 1 else 0 := by
  simp only [orbitSum, Finsupp.finset_sum_apply, Finsupp.single_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hne; exact if_neg hne
    · intro ha
      exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ a, h⟩) ha
  · apply Finset.sum_eq_zero
    intro b hb
    rw [Finset.mem_filter] at hb
    exact if_neg (fun heq : b = a => h (heq ▸ hb.2))

theorem orbitSum_mem_invariantSubspace (O : orbitRel.Quotient G α) :
    orbitSum O ∈ invariantSubspace G α := by
  rw [invariant_iff_constant_on_orbits]
  intro a b hab
  rw [orbitSum_apply, orbitSum_apply]
  have hiff : a ∈ orbitRel.Quotient.orbit O ↔ b ∈ orbitRel.Quotient.orbit O := by
    simp only [orbitRel.Quotient.mem_orbit]
    exact ⟨fun h => hab ▸ h, fun h => hab.symm ▸ h⟩
  by_cases ha : a ∈ orbitRel.Quotient.orbit O
  · rw [if_pos ha, if_pos (hiff.mp ha)]
  · rw [if_neg ha, if_neg (mt hiff.mpr ha)]

omit [Fintype α] [DecidableEq α] in
theorem quotient_eq_of_mem_orbit {a : α} {O : orbitRel.Quotient G α}
    (h : a ∈ orbitRel.Quotient.orbit O) :
    (Quotient.mk'' a : orbitRel.Quotient G α) = O :=
  orbitRel.Quotient.mem_orbit.mp h

omit [DecidableEq α] in

theorem sum_orbit_indicator (c : orbitRel.Quotient G α → ℝ) (a : α)
    (O₀ : orbitRel.Quotient G α)
    (ha : a ∈ orbitRel.Quotient.orbit O₀) :
    (∑ O : orbitRel.Quotient G α,
      c O * if a ∈ orbitRel.Quotient.orbit O then (1 : ℝ) else 0) = c O₀ := by
  rw [Finset.sum_eq_single O₀]
  · rw [if_pos ha, mul_one]
  · intro O' _ hO'
    have : ¬(a ∈ orbitRel.Quotient.orbit O') := by
      intro hmem
      exact hO' ((quotient_eq_of_mem_orbit hmem).symm.trans (quotient_eq_of_mem_orbit ha))
    rw [if_neg this, mul_zero]
  · intro habs; exact absurd (Finset.mem_univ _) habs

theorem orbitSum_linearIndependent :
    LinearIndependent ℝ (fun O : orbitRel.Quotient G α =>
      (⟨orbitSum O, orbitSum_mem_invariantSubspace O⟩ :
        ↥(invariantSubspace G α))) := by
  rw [Fintype.linearIndependent_iffₛ]
  intro f g hfg O
  obtain ⟨a, ha⟩ := orbitRel.Quotient.nonempty_orbit O
  have hval : (∑ O', f O' • (⟨orbitSum O', orbitSum_mem_invariantSubspace O'⟩ :
      ↥(invariantSubspace G α))).val =
    (∑ O', g O' • (⟨orbitSum O', orbitSum_mem_invariantSubspace O'⟩ :
      ↥(invariantSubspace G α))).val := congrArg Subtype.val hfg
  have heq := DFunLike.congr_fun hval a
  simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul, Finsupp.finset_sum_apply,
    Finsupp.smul_apply, smul_eq_mul, orbitSum_apply] at heq
  rw [sum_orbit_indicator f a O ha, sum_orbit_indicator g a O ha] at heq
  exact heq

theorem orbitSum_span :
    ⊤ ≤ Submodule.span ℝ (Set.range (fun O : orbitRel.Quotient G α =>
      (⟨orbitSum O, orbitSum_mem_invariantSubspace O⟩ :
        ↥(invariantSubspace G α)))) := by
  intro ⟨v, hv⟩ _
  suffices hkey : v = ∑ O : orbitRel.Quotient G α, v (rep G α O) • orbitSum O by
    have hmem : (⟨v, hv⟩ : ↥(invariantSubspace G α)) =
        ∑ O : orbitRel.Quotient G α,
          v (rep G α O) • ⟨orbitSum O, orbitSum_mem_invariantSubspace O⟩ := by
      apply Subtype.ext
      simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul]
      exact hkey
    rw [hmem]
    exact Submodule.sum_mem _ (fun O _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨O, rfl⟩))
  ext a
  simp only [Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul, orbitSum_apply]
  have ha : a ∈ orbitRel.Quotient.orbit
      (Quotient.mk'' a : orbitRel.Quotient G α) := by
    rw [orbitRel.Quotient.orbit_mk]; exact mem_orbit_self a
  rw [sum_orbit_indicator _ a _ ha]
  symm
  exact invariant_iff_constant_on_orbits.mp hv _ a (mk_rep G α _)

end OrbitBasis
end
