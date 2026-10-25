/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/PermCycleQuotientCount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialRibbonBoundaryParity.Part3
import Def.StatisticalMechanics.Code.FrontierA.PermCycleQuotientCount.Part2


namespace StatMech.FrontierA

open Equiv

variable {D : Type*} [Fintype D] [DecidableEq D]


theorem natCard_permCycleClass (sigma : Perm D) :
    Nat.card (PermCycleClass sigma) = permCycleCount sigma := by
  classical
  rw [Nat.card_congr (permCycleClassEquivRepresentative sigma),
    Nat.card_eq_fintype_card, Fintype.card_sum,
    Fintype.card_coe, Equiv.Perm.card_fixedPoints]
  unfold permCycleCount
  rw [Equiv.Perm.cycleType_def, Multiset.card_map, Finset.card_def]

theorem two_not_mem_cycleType_of_sq_ne
    (sigma : Perm D) (h2 : ∀ x, (sigma ^ 2) x ≠ x) :
    2 ∉ sigma.cycleType := by
  intro hmem
  simp only [Equiv.Perm.cycleType_def, ← Finset.mem_def,
    Function.comp_apply, Multiset.mem_map,
    Equiv.Perm.mem_cycleFactorsFinset_iff] at hmem
  obtain ⟨c, ⟨hc, hagree⟩, hcard⟩ := hmem
  obtain ⟨x, hx⟩ := hc.nonempty_support
  have hcx : c x = sigma x := hagree x hx
  have hcx_mem : c x ∈ c.support := Equiv.Perm.apply_mem_support.mpr hx
  have hccx : c (c x) = sigma (c x) := hagree (c x) hcx_mem
  have horder : orderOf c = 2 := hc.orderOf.trans hcard
  have hcpow : c ^ 2 = 1 := by
    apply orderOf_dvd_iff_pow_eq_one.mp
    rw [horder]
  apply h2 x
  rw [pow_two, Equiv.Perm.mul_apply, ← hcx, ← hccx]
  change (c ^ 2) x = x
  rw [hcpow]
  rfl


theorem four_mul_permCycleCount_eq_card_of_pow_four_eq_one_of_sq_ne
    (sigma : Perm D) (h4 : sigma ^ 4 = 1)
    (h2 : ∀ x, (sigma ^ 2) x ≠ x) :
    4 * permCycleCount sigma = Fintype.card D := by
  have hne2 := two_not_mem_cycleType_of_sq_ne sigma h2
  have hall : ∀ n ∈ sigma.cycleType, n = 4 := by
    intro n hn
    have hnlow := Equiv.Perm.two_le_of_mem_cycleType hn
    have hndiv : n ∣ 4 :=
      (Equiv.Perm.dvd_of_mem_cycleType hn).trans
        (orderOf_dvd_of_pow_eq_one h4)
    have hnnot : n ≠ 2 := fun h => hne2 (h ▸ hn)
    have hnle : n ≤ 4 := Nat.le_of_dvd (by norm_num) hndiv
    interval_cases n
    · exact (hnnot rfl).elim
    · norm_num at hndiv
    · rfl
  have htype : sigma.cycleType =
      Multiset.replicate sigma.cycleType.card 4 :=
    Multiset.eq_replicate.mpr ⟨rfl, hall⟩
  have hsupp : sigma.support = Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro x
    apply Equiv.Perm.mem_support.mpr
    intro hx
    apply h2 x
    simp [pow_two, Equiv.Perm.mul_apply, hx]
  have hsum : sigma.cycleType.sum = Fintype.card D := by
    rw [sigma.sum_cycleType, hsupp, Finset.card_univ]
  have hcycles : sigma.cycleType.card * 4 = Fintype.card D := by
    rw [← hsum, htype, Multiset.sum_replicate]
    simp
  unfold permCycleCount
  rw [hsum, Nat.sub_self, Nat.add_zero]
  omega

end StatMech.FrontierA
