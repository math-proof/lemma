/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc4_occursrestrictwitness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc3_core.Part3
import Theorem.StatisticalMechanics.Code.Inequalities.PerOrbitCardClose.Part8
import Theorem.StatisticalMechanics.Code.Walls.rc2_slabimgeqinter.Part3
import Def.StatisticalMechanics.Code.Walls.rc4_occursrestrictwitness.Part5
open Finset
open scoped StatMech


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*}


@[simp] theorem mem_pocRestrictWitness (k : ConfigSpace α × ConfigSpace α) (K : Set α)
    (s : DifferSub k) : s ∈ pocRestrictWitness k K ↔ s.1 ∈ K := Iff.rfl


theorem rc4_agreeOn_unrestrict_of_restrict {k : ConfigSpace α × ConfigSpace α}
    {K : Set α} {ω : ConfigSpace α} {σ' : ConfigSpace (DifferSub k)}
    (hfroz : ∀ a, k.1 a = k.2 a → ω a = k.1 a)
    (hagree : agreeOn (pocRestrictWitness k K) (pocRestrict k ω) σ') :
    agreeOn K ω (pocUnrestrict k σ') := by
  intro a haK
  by_cases h : k.1 a ≠ k.2 a
  · 
    rw [pocUnrestrict_apply_differ k σ' h]
    exact hagree ⟨a, h⟩ haK
  · 
    rw [not_ne_iff] at h
    rw [pocUnrestrict_apply_nondiffer k σ' h, hfroz a h]


theorem rc4_occurs_restrict_witness_frozen {k : ConfigSpace α × ConfigSpace α}
    {A : Set (ConfigSpace α)} {K : Set α} {ω : ConfigSpace α}
    (hfroz : ∀ a, k.1 a = k.2 a → ω a = k.1 a)
    (hocc : OccursOn A K ω) :
    OccursOn (pocFrozenRestrict k A) (pocRestrictWitness k K) (pocRestrict k ω) := by
  intro σ' hagree
  rw [mem_pocFrozenRestrict]
  exact hocc _ (rc4_agreeOn_unrestrict_of_restrict hfroz hagree)


theorem rc4_occurs_restrict_witness {k : ConfigSpace α × ConfigSpace α}
    {A : Set (ConfigSpace α)} {K : Set α} {ω : ConfigSpace α}
    (hslab : ω ∈ rc2_slab k) (hocc : OccursOn A K ω) :
    OccursOn (pocFrozenRestrict k A) (pocRestrictWitness k K) (pocRestrict k ω) :=
  rc4_occurs_restrict_witness_frozen (fun a ha => rc3_core_slab_frozen hslab a ha) hocc


theorem topKey_differ (a : α) : (poc_topKey : ConfigSpace α × ConfigSpace α).1 a ≠ poc_topKey.2 a :=
  by simp [poc_topKey]


theorem pocUnrestrict_pocRestrict_top (ω : ConfigSpace α) :
    pocUnrestrict (poc_topKey : ConfigSpace α × ConfigSpace α) (pocRestrict poc_topKey ω) = ω := by
  funext a
  rw [pocUnrestrict_apply_differ _ _ (topKey_differ a)]
  rfl


theorem rc4_occurs_restrict_witness_top {A : Set (ConfigSpace α)} {K : Set α} {ω : ConfigSpace α}
    (hocc : OccursOn A K ω) :
    OccursOn (pocFrozenRestrict (poc_topKey : ConfigSpace α × ConfigSpace α) A)
      (pocRestrictWitness poc_topKey K) (pocRestrict poc_topKey ω) :=
  rc4_occurs_restrict_witness_frozen
    (fun a ha => absurd ha (topKey_differ a)) hocc

end StatMech.Walls
