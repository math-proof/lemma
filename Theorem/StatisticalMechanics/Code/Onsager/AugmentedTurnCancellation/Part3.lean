/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/AugmentedTurnCancellation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationSpinGauge.Part5
import Def.StatisticalMechanics.Code.Onsager.AugmentedTurnCancellation.Part2


namespace StatMech.Onsager

open BigOperators

theorem ons_loopWeight_stateWeightedReversibleTurnMatrix
    {E : Type*} [Fintype E] [DecidableEq E]
    {n : ℕ} [NeZero n]
    (dir : E → Fin 4) (omega : ℂ)
    (rowWeight colWeight : E → ℂ) (q : E → E → ℂ)
    (loop : Fin n → E) :
    ons_loopWeight
        (ons_stateWeightedReversibleTurnMatrix
          dir omega rowWeight colWeight q) loop =
      (∏ k, rowWeight (loop k) * colWeight (loop k)) *
        (∏ k, q (loop k) (loop (k + 1))) *
          ∏ k, ons_turnW omega (dir (loop (k + 1))) (dir (loop k)) := by
  have hcol : (∏ k, colWeight (loop (k + 1))) =
      ∏ k, colWeight (loop k) :=
    Equiv.prod_comp (Equiv.addRight (1 : Fin n))
      (fun k ↦ colWeight (loop k))
  unfold ons_loopWeight ons_stateWeightedReversibleTurnMatrix
  rw [show (∏ k, rowWeight (loop k) * colWeight (loop (k + 1)) *
        q (loop k) (loop (k + 1)) *
          ons_turnW omega (dir (loop (k + 1))) (dir (loop k))) =
      (∏ k, rowWeight (loop k)) *
        (∏ k, colWeight (loop (k + 1))) *
        (∏ k, q (loop k) (loop (k + 1))) *
        ∏ k, ons_turnW omega (dir (loop (k + 1))) (dir (loop k)) by
      simp_rw [Finset.prod_mul_distrib]]
  rw [hcol, ← Finset.prod_mul_distrib]

theorem ons_stateWeightedReversibleTurnMatrix_surgery_sign
    {E : Type*} [Fintype E] [DecidableEq E]
    {n : ℕ} [NeZero n]
    (rev : E → E) (hrev : Function.Involutive rev)
    (dir : E → Fin 4) (hdir : ∀ e, dir (rev e) = dir e + 2)
    (omega : ℂ) (homega : omega ≠ 0) (hI : omega ^ 2 = Complex.I)
    (rowWeight colWeight : E → ℂ)
    (hweight : ∀ x,
      rowWeight (rev x) * colWeight (rev x) =
        rowWeight x * colWeight x)
    (q : E → E → ℂ)
    (hq : ∀ x y, q (rev y) (rev x) = q x y)
    (e : E) (loop : Fin n → E)
    (hloop : (∃ i, loop i = e) ∧ (∃ j, loop j = rev e)) :
    ons_loopWeight
        (ons_stateWeightedReversibleTurnMatrix
          dir omega rowWeight colWeight q)
        (ons_surgery e rev loop) =
      -ons_loopWeight
        (ons_stateWeightedReversibleTurnMatrix
          dir omega rowWeight colWeight q) loop := by
  rw [ons_loopWeight_stateWeightedReversibleTurnMatrix,
    ons_loopWeight_stateWeightedReversibleTurnMatrix]
  rw [ons_invariantStateProduct_surgery rev hrev
      (fun x ↦ rowWeight x * colWeight x) hweight e loop hloop,
    ons_reversibleFactorProduct_surgery rev hrev dir hdir q hq e loop hloop,
    ons_turnProduct_surgery_sign rev hrev dir hdir omega homega hI e loop hloop]
  ring

theorem ons_stateWeightedReversibleTurnMatrix_lemma5
    {E : Type*} [Fintype E] [DecidableEq E]
    {n : ℕ} [NeZero n]
    (rev : E → E) (hrev : Function.Involutive rev)
    (dir : E → Fin 4) (hdir : ∀ e, dir (rev e) = dir e + 2)
    (omega : ℂ) (homega : omega ≠ 0) (hI : omega ^ 2 = Complex.I)
    (rowWeight colWeight : E → ℂ)
    (hweight : ∀ x,
      rowWeight (rev x) * colWeight (rev x) =
        rowWeight x * colWeight x)
    (q : E → E → ℂ)
    (hq : ∀ x y, q (rev y) (rev x) = q x y)
    (e : E) (hrne : rev e ≠ e) :
    ∑ loop ∈ ons_loopSetBoth (n := n) e (rev e),
        ons_loopWeight
          (ons_stateWeightedReversibleTurnMatrix
            dir omega rowWeight colWeight q) loop = 0 := by
  apply ons_lemma5 _ e rev hrev hrne
  intro loop hloop
  apply ons_stateWeightedReversibleTurnMatrix_surgery_sign
      rev hrev dir hdir omega homega hI
      rowWeight colWeight hweight q hq e loop
  simpa only [ons_mem_loopSetBoth] using hloop


theorem ons_cyclicTurnProduct_omega_inv
    {n : ℕ} [NeZero n] (omega : ℂ)
    (homega : omega ≠ 0) (hI : omega ^ 2 = Complex.I)
    (d : Fin n → Fin 4) :
    (∏ k, ons_turnW omega⁻¹ (d (k + 1)) (d k)) =
      ∏ k, ons_turnW omega (d (k + 1)) (d k) := by
  by_cases hu : ∃ k : Fin n, d k = d (k + 1) + 2
  · obtain ⟨k, hk⟩ := hu
    have hzInv : ons_turnW omega⁻¹ (d (k + 1)) (d k) = 0 := by
      rw [hk]
      exact ons_turnW_uturn omega⁻¹ _
    have hz : ons_turnW omega (d (k + 1)) (d k) = 0 := by
      rw [hk]
      exact ons_turnW_uturn omega _
    rw [Finset.prod_eq_zero (Finset.mem_univ k) hzInv,
      Finset.prod_eq_zero (Finset.mem_univ k) hz]
  · push_neg at hu
    have hp : (∏ k, ons_turnW omega (d (k + 1)) (d k)) =
        omega ^ (∑ k, ons_turnPow (d (k + 1)) (d k)) := by
      rw [← ons_prod_zpow omega homega]
      exact Finset.prod_congr rfl
        (fun k _ ↦ ons_turnW_eq_zpow omega _ _ (hu k))
    have hpInv : (∏ k, ons_turnW omega⁻¹ (d (k + 1)) (d k)) =
        omega⁻¹ ^ (∑ k, ons_turnPow (d (k + 1)) (d k)) := by
      rw [← ons_prod_zpow omega⁻¹ (inv_ne_zero homega)]
      exact Finset.prod_congr rfl
        (fun k _ ↦ ons_turnW_eq_zpow omega⁻¹ _ _ (hu k))
    rw [hp, hpInv]
    set S := ∑ k, ons_turnPow (d (k + 1)) (d k) with hS
    have hScast : ((S : ℤ) : ZMod 4) = 0 := by
      have hterm : ∀ k : Fin n,
          (((ons_turnPow (d (k + 1)) (d k) : ℤ)) : ZMod 4) =
            ((d k : Fin 4) : ZMod 4) -
              ((d (k + 1) : Fin 4) : ZMod 4) := by
        intro k
        rw [ons_turnPow_cast _ _ (hu k)]
        rfl
      have hshift : (∑ k, ((d (k + 1) : Fin 4) : ZMod 4)) =
          ∑ k, ((d k : Fin 4) : ZMod 4) :=
        Equiv.sum_comp (Equiv.addRight (1 : Fin n))
          (fun k ↦ ((d k : Fin 4) : ZMod 4))
      rw [hS, Int.cast_sum]
      calc
        (∑ k, ((ons_turnPow (d (k + 1)) (d k) : ℤ) : ZMod 4)) =
            ∑ k, (((d k : Fin 4) : ZMod 4) -
              ((d (k + 1) : Fin 4) : ZMod 4)) :=
          Finset.sum_congr rfl (fun k _ ↦ hterm k)
        _ = (∑ k, ((d k : Fin 4) : ZMod 4)) -
            ∑ k, ((d (k + 1) : Fin 4) : ZMod 4) := by
          rw [Finset.sum_sub_distrib]
        _ = 0 := by rw [hshift, sub_self]
    obtain ⟨m, hm⟩ : ∃ m : ℤ, S = 4 * m := by
      obtain ⟨m, hm⟩ :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd S 4).mp hScast
      exact ⟨m, by exact_mod_cast hm⟩
    have h4 : omega ^ (4 : ℤ) = -1 := by
      rw [show (4 : ℤ) = ((4 : ℕ) : ℤ) from rfl, zpow_natCast]
      exact ons_omega_pow_four omega hI
    rw [hm, _root_.zpow_mul, _root_.zpow_mul,
      _root_.inv_zpow, h4]
    simp

end StatMech.Onsager
