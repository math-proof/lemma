/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TurningTelescope.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.KWMatrix
import Def.StatisticalMechanics.Code.Onsager.TurningTelescope.Part3


namespace StatMech.Onsager

theorem ons_turnW_eq_zpow (ω : ℂ) (μ ν : Fin 4) (h : ν ≠ μ + 2) :
    ons_turnW ω μ ν = ω ^ (ons_turnPow μ ν) := by
  unfold ons_turnW ons_turnPow
  by_cases h0 : ν = μ
  · simp [h0]
  · by_cases h1 : ν = μ + 1
    · simp [h1]
    · rw [if_neg h0, if_neg h1, if_neg h, if_neg h0, if_neg h1, if_neg h]
      simp


theorem ons_prod_zpow (ω : ℂ) (hω : ω ≠ 0) {ι : Type*} (s : Finset ι) (f : ι → ℤ) :
    ∏ i ∈ s, ω ^ (f i) = ω ^ (∑ i ∈ s, f i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s ha ih
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, ← zpow_add₀ hω]


theorem ons_turnPow_cast (μ ν : Fin 4) (h : ν ≠ μ + 2) :
    ((ons_turnPow μ ν : ℤ) : ZMod 4) = ons_turnZ μ ν := by
  revert h
  fin_cases μ <;> fin_cases ν <;> decide


theorem ons_walk_prod_eq (ω : ℂ) (hω : ω ≠ 0) (n : ℕ) (d : Fin (n + 1) → Fin 4)
    (hnu : ∀ k : Fin n, d k.succ ≠ d k.castSucc + 2) :
    ∏ k : Fin n, ons_turnW ω (d k.castSucc) (d k.succ)
      = ω ^ (∑ k : Fin n, ons_turnPow (d k.castSucc) (d k.succ)) := by
  rw [← ons_prod_zpow ω hω]
  apply Finset.prod_congr rfl
  intro k _
  exact ons_turnW_eq_zpow ω (d k.castSucc) (d k.succ) (hnu k)


theorem ons_walk_turnPow_mod (n : ℕ) (d : Fin (n + 1) → Fin 4)
    (hnu : ∀ k : Fin n, d k.succ ≠ d k.castSucc + 2) :
    ((∑ k : Fin n, ons_turnPow (d k.castSucc) (d k.succ) : ℤ) : ZMod 4)
      = (d (Fin.last n) : ZMod 4) - (d 0 : ZMod 4) := by
  rw [Int.cast_sum, ← ons_turnZ_telescope n d]
  apply Finset.sum_congr rfl
  intro k _
  rw [ons_turnPow_cast (d k.castSucc) (d k.succ) (hnu k)]
  rfl


theorem ons_omega_pow_four (ω : ℂ) (h : ω ^ 2 = Complex.I) : ω ^ 4 = -1 := by
  have h4 : ω ^ 4 = (ω ^ 2) ^ 2 := by ring
  rw [h4, h, Complex.I_sq]


theorem ons_walk_prod_antipodal (ω : ℂ) (hω : ω ≠ 0) (hI : ω ^ 2 = Complex.I)
    (n : ℕ) (d : Fin (n + 1) → Fin 4)
    (hnu : ∀ k : Fin n, d k.succ ≠ d k.castSucc + 2)
    (hend : d (Fin.last n) = d 0 + 2) :
    ∃ m : ℤ, ∏ k : Fin n, ons_turnW ω (d k.castSucc) (d k.succ)
      = (-1) ^ m * Complex.I := by
  
  have hmod : ((∑ k : Fin n, ons_turnPow (d k.castSucc) (d k.succ) : ℤ) : ZMod 4) = 2 := by
    rw [ons_walk_turnPow_mod n d hnu, hend]
    generalize d 0 = a
    fin_cases a <;> rfl
  
  obtain ⟨m, hm⟩ : ∃ m : ℤ,
      (∑ k : Fin n, ons_turnPow (d k.castSucc) (d k.succ)) = 4 * m + 2 := by
    have hzero : (((∑ k : Fin n, ons_turnPow (d k.castSucc) (d k.succ)) - 2 : ℤ)
        : ZMod 4) = 0 := by
      rw [Int.cast_sub, hmod]
      decide
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hzero
    obtain ⟨k, hk⟩ := hzero
    exact ⟨k, by push_cast at hk; linarith⟩
  refine ⟨m, ?_⟩
  rw [ons_walk_prod_eq ω hω n d hnu, hm, zpow_add₀ hω, zpow_mul]
  have h4 : ω ^ (4 : ℤ) = -1 := by
    rw [show (4 : ℤ) = ((4 : ℕ) : ℤ) from rfl, zpow_natCast]
    exact ons_omega_pow_four ω hI
  have h2 : ω ^ (2 : ℤ) = Complex.I := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast]
    exact hI
  rw [h4, h2]

end StatMech.Onsager
