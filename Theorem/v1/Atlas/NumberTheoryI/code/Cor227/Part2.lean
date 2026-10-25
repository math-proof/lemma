/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor227.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.NumberTheoryI.code.Prop226
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.Prop226
import Def.v1.Atlas.NumberTheoryI.code.Cor227


noncomputable section

open scoped NumberField

namespace RayClassField

universe u

variable {K : Type u} [Field K] [NumberField K]

lemma Modulus.gcd_weight_lt_of_not_dvd {𝔪₁ 𝔪₂ : Modulus K}
    (h : ¬ 𝔪₁.dvd 𝔪₂) : (𝔪₁.gcd 𝔪₂).weight < 𝔪₁.weight := by
  simp only [Modulus.dvd, not_forall, not_le] at h
  obtain ⟨v₀, hv₀⟩ := h
  have hgcd_v₀ : (𝔪₁.gcd 𝔪₂).toFun v₀ < 𝔪₁.toFun v₀ := by
    simp only [Modulus.gcd]
    exact lt_of_le_of_lt (min_le_right _ _) hv₀
  have hgcd_le : ∀ v, (𝔪₁.gcd 𝔪₂).toFun v ≤ 𝔪₁.toFun v := fun v => by
    simp only [Modulus.gcd]; exact min_le_left _ _
  have hv₀_supp : v₀ ∈ 𝔪₁.finite_support.toFinset := by
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    omega
  have hsub : (𝔪₁.gcd 𝔪₂).finite_support.toFinset ⊆ 𝔪₁.finite_support.toFinset := by
    intro v hv
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hv ⊢
    intro heq
    exact hv (by simp only [Modulus.gcd]; omega)
  unfold Modulus.weight
  calc (𝔪₁.gcd 𝔪₂).finite_support.toFinset.sum (𝔪₁.gcd 𝔪₂).toFun
      ≤ 𝔪₁.finite_support.toFinset.sum (𝔪₁.gcd 𝔪₂).toFun := by
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
    _ < 𝔪₁.finite_support.toFinset.sum 𝔪₁.toFun := by
        exact Finset.sum_lt_sum (fun v _ => hgcd_le v) ⟨v₀, hv₀_supp, hgcd_v₀⟩

theorem corollary_22_7_existence (p : CongruenceSubgroupPair K) :
    ∃ p₀ : CongruenceSubgroupPair K,
      p.IsEquiv p₀ ∧
      ∀ q : CongruenceSubgroupPair K, p.IsEquiv q → p₀.modulus.dvd q.modulus := by
  suffices h : ∀ (n : ℕ) (p : CongruenceSubgroupPair K),
      p.modulus.weight = n →
      ∃ p₀ : CongruenceSubgroupPair K,
        p.IsEquiv p₀ ∧
        ∀ q : CongruenceSubgroupPair K, p.IsEquiv q → p₀.modulus.dvd q.modulus from
    h p.modulus.weight p rfl
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro p hp_wt
  by_cases hmin : ∀ q : CongruenceSubgroupPair K, p.IsEquiv q → p.modulus.dvd q.modulus
  · exact ⟨p, p.isEquiv_refl, hmin⟩
  · push Not at hmin

    obtain ⟨q, hpq, hndvd⟩ := hmin
    obtain ⟨r, hr_mod, hpr, hqr⟩ := proposition_22_6 p q hpq
    have hr_wt_lt : r.modulus.weight < n := by
      rw [← hp_wt, hr_mod]
      exact Modulus.gcd_weight_lt_of_not_dvd hndvd
    obtain ⟨p₀, hrp₀, hp₀_min⟩ := ih r.modulus.weight hr_wt_lt r rfl
    have hpp₀ : p.IsEquiv p₀ := hpr.trans' hrp₀
    refine ⟨p₀, hpp₀, fun s hps => ?_⟩
    have hrs : r.IsEquiv s := hpr.symm'.trans' hps
    exact hp₀_min s hrs

theorem corollary_22_7_modulus_unique (p p₀ p₀' : CongruenceSubgroupPair K)
    (hp₀ : p.IsEquiv p₀)
    (hp₀_min : ∀ q, p.IsEquiv q → p₀.modulus.dvd q.modulus)
    (hp₀' : p.IsEquiv p₀')
    (hp₀'_min : ∀ q, p.IsEquiv q → p₀'.modulus.dvd q.modulus) :
    p₀.modulus = p₀'.modulus :=
  Modulus.dvd_antisymm' (hp₀_min p₀' hp₀') (hp₀'_min p₀ hp₀)

theorem corollary_22_7 (p : CongruenceSubgroupPair K) :
    ∃! (𝔠 : Modulus K),
      (∃ p₀ : CongruenceSubgroupPair K, p₀.modulus = 𝔠 ∧ p.IsEquiv p₀) ∧
      (∀ q : CongruenceSubgroupPair K, p.IsEquiv q → 𝔠.dvd q.modulus) := by
  obtain ⟨p₀, hp₀_equiv, hp₀_min⟩ := corollary_22_7_existence p
  refine ⟨p₀.modulus, ⟨⟨p₀, rfl, hp₀_equiv⟩, hp₀_min⟩, ?_⟩
  intro 𝔠' ⟨⟨p₀', hp₀'_mod, hp₀'_equiv⟩, hp₀'_min⟩
  have : p₀.modulus = p₀'.modulus :=
    corollary_22_7_modulus_unique p p₀ p₀'
      hp₀_equiv hp₀_min
      hp₀'_equiv (fun q hq => hp₀'_mod ▸ hp₀'_min q hq)
  rw [← hp₀'_mod, ← this]

end RayClassField
end
