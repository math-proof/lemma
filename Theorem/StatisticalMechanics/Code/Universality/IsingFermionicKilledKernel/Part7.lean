/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKilledKernel.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicStoppedWalk.Part6
import Def.StatisticalMechanics.Code.Universality.IsingFermionicKilledKernel.Part7


namespace StatMech.Universality

open Finset

noncomputable section

theorem isingBinomialWeight_le_middle (t k : Nat) :
    isingBinomialWeight t k ≤ isingBinomialMiddleWeight t := by
  unfold isingBinomialWeight isingBinomialMiddleWeight
  exact div_le_div_of_nonneg_right
    (by exact_mod_cast Nat.choose_le_middle k t) (by positivity)

theorem isingBinomialMiddleWeight_nonneg (t : Nat) :
    0 ≤ isingBinomialMiddleWeight t := by
  unfold isingBinomialMiddleWeight
  positivity

theorem isingLineBinomialKernel_nonneg (t : Nat) (x y : Int) :
    0 ≤ isingLineBinomialKernel t x y := by
  unfold isingLineBinomialKernel
  apply Finset.sum_nonneg
  intro k hk
  split_ifs
  · unfold isingBinomialWeight
    positivity
  · exact le_rfl

theorem isingLineBinomialKernel_le_middle
    (t : Nat) (x y : Int) :
    isingLineBinomialKernel t x y ≤ isingBinomialMiddleWeight t := by
  by_cases h : ∃ k ∈ range (t + 1),
      y = x + 2 * (k : Int) - (t : Int)
  · rcases h with ⟨k, hk, heq⟩
    unfold isingLineBinomialKernel
    rw [Finset.sum_eq_single k]
    · simp [heq]
      exact isingBinomialWeight_le_middle t k
    · intro b hb hbk
      have hbne : ¬y = x + 2 * (b : Int) - (t : Int) := by
        intro hbeq
        have hcast : (b : Int) = k := by omega
        have : b = k := by exact_mod_cast hcast
        exact hbk this
      simp [hbne]
    · exact fun hknot ↦ (hknot hk).elim
  · have hzero : isingLineBinomialKernel t x y = 0 := by
      unfold isingLineBinomialKernel
      apply Finset.sum_eq_zero
      intro k hk
      have hkne : ¬y = x + 2 * (k : Int) - (t : Int) := by
        intro hkeq
        exact h ⟨k, hk, hkeq⟩
      simp [hkne]
    rw [hzero]
    exact isingBinomialMiddleWeight_nonneg t

theorem ising_odd_choose_le_two_mul_centralBinom (n : Nat) :
    (2 * n + 1).choose n ≤ 2 * Nat.centralBinom n := by
  by_cases hn : n = 0
  · subst n
    norm_num [Nat.centralBinom]
  · have hp := Nat.choose_succ_succ (2 * n) (n - 1)
    have hle := Nat.choose_le_middle (n - 1) (2 * n)
    rw [show (2 * n) / 2 = n by omega,
      ← Nat.centralBinom_eq_two_mul_choose] at hle
    calc
      (2 * n + 1).choose n =
          (2 * n).choose (n - 1) + (2 * n).choose n := by
        have hs : (n - 1).succ = n := by omega
        rw [hs] at hp
        simpa using hp
      _ ≤ Nat.centralBinom n + Nat.centralBinom n :=
        Nat.add_le_add hle (by rfl)
      _ = 2 * Nat.centralBinom n := by omega

theorem isingBinomialMiddleWeight_sq_le (t : Nat) :
    isingBinomialMiddleWeight t ^ 2 ≤ 2 / (t + 1 : Real) := by
  rcases Nat.even_or_odd t with ⟨n, hn⟩ | ⟨n, hn⟩
  · subst t
    rw [show isingBinomialMiddleWeight (n + n) =
        (Nat.centralBinom n : Real) / 4 ^ n by
      unfold isingBinomialMiddleWeight Nat.centralBinom
      rw [show (n + n) / 2 = n by omega,
        show n + n = 2 * n by omega]
      rw [show (2 : Real) ^ (2 * n) = 4 ^ n by
        rw [show (4 : Real) = 2 ^ 2 by norm_num, ← pow_mul]]]
    rw [div_pow]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    have hc := isingCentralBinom_sq_mul_le n
    have hp : ((4 : Real) ^ n) ^ 2 = (16 : Real) ^ n := by
      rw [pow_two, ← mul_pow]
      norm_num
    norm_num [Nat.cast_add] at *
    nlinarith [sq_nonneg (Nat.centralBinom n : Real)]
  · subst t
    rw [show isingBinomialMiddleWeight (2 * n + 1) =
        ((2 * n + 1).choose n : Real) / (2 * 4 ^ n) by
      unfold isingBinomialMiddleWeight
      rw [show (2 * n + 1) / 2 = n by omega, pow_succ]
      congr 1
      rw [show (2 : Real) ^ (2 * n) = 4 ^ n by
        rw [show (4 : Real) = 2 ^ 2 by norm_num, ← pow_mul]]
      ring]
    rw [div_pow]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    have hc := isingCentralBinom_sq_mul_le n
    have hdNat := ising_odd_choose_le_two_mul_centralBinom n
    have hd : ((2 * n + 1).choose n : Real) ≤
        2 * (Nat.centralBinom n : Real) := by
      exact_mod_cast hdNat
    have hd0 : (0 : Real) ≤ ((2 * n + 1).choose n : Real) := by positivity
    have hc0 : (0 : Real) ≤ Nat.centralBinom n := by positivity
    have hd2 : ((2 * n + 1).choose n : Real) ^ 2 ≤
        (2 * (Nat.centralBinom n : Real)) ^ 2 :=
      (sq_le_sq₀ hd0 (mul_nonneg (by norm_num) hc0)).2 hd
    have hcn : (Nat.centralBinom n : Real) ^ 2 * (n + 1) ≤ 16 ^ n := by
      calc
        _ ≤ (Nat.centralBinom n : Real) ^ 2 * (2 * (n : Real) + 1) := by
          have hn0 : (0 : Real) ≤ n := by positivity
          have hnle : (n : Real) + 1 ≤ 2 * (n : Real) + 1 := by nlinarith
          exact mul_le_mul_of_nonneg_left hnle (sq_nonneg _)
        _ ≤ _ := hc
    have hp : ((4 : Real) ^ n) ^ 2 = (16 : Real) ^ n := by
      rw [pow_two, ← mul_pow]
      norm_num
    norm_num [Nat.cast_add, Nat.cast_mul] at *
    nlinarith [mul_le_mul_of_nonneg_right hd2
      (show (0 : Real) ≤ n + 1 by positivity)]

theorem isingLineBinomialKernel_sq_le (t : Nat) (x y : Int) :
    isingLineBinomialKernel t x y ^ 2 ≤ 2 / (t + 1 : Real) := by
  exact le_trans
    ((sq_le_sq₀ (isingLineBinomialKernel_nonneg t x y)
      (isingBinomialMiddleWeight_nonneg t)).2
        (isingLineBinomialKernel_le_middle t x y))
    (isingBinomialMiddleWeight_sq_le t)


theorem isingLeapfrogFreeKernel_le (t : Nat)
    (p q : IsingLeapfrogPlane) :
    isingLeapfrogFreeKernel t p q ≤ 2 / (t + 1 : Real) := by
  rw [isingLeapfrogFreeKernel_eq_binomial]
  unfold isingLeapfrogFreeBinomialKernel
  have hx0 := isingLineBinomialKernel_nonneg t p.1 q.1
  have hy0 := isingLineBinomialKernel_nonneg t p.2 q.2
  have hx := isingLineBinomialKernel_sq_le t p.1 q.1
  have hy := isingLineBinomialKernel_sq_le t p.2 q.2
  have hC : 0 ≤ 2 / (t + 1 : Real) := by positivity
  nlinarith [sq_nonneg
    (isingLineBinomialKernel t p.1 q.1 -
      isingLineBinomialKernel t p.2 q.2)]

end
end StatMech.Universality
