/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalBallot.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicStoppedPointwise.Part3


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

theorem choose_right_mono_to_middle (n : Nat) :
    ∀ {k i : Nat}, k ≤ i → i ≤ n / 2 → n.choose k ≤ n.choose i := by
  intro k i hki him
  induction i, hki using Nat.le_induction with
  | base => exact le_rfl
  | succ i hki ih =>
      have hi : i < n / 2 := by omega
      have hfactor : i + 1 ≤ n - i := by omega
      have hmul : n.choose i * (i + 1) ≤ n.choose i * (n - i) :=
        Nat.mul_le_mul_left _ hfactor
      rw [← Nat.choose_succ_right_eq] at hmul
      exact le_trans (ih (by omega))
        (Nat.le_of_mul_le_mul_right hmul (by omega))

theorem choose_mul_middle_block_le_two_pow
    (n k : Nat) (hk : k ≤ n / 2) :
    (n / 2 - k + 1) * n.choose k ≤ 2 ^ n := by
  let block := Finset.Icc k (n / 2)
  have hterm : ∀ i ∈ block, n.choose k ≤ n.choose i := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    exact choose_right_mono_to_middle n hi.1 hi.2
  have hsum : (∑ i ∈ block, n.choose k) ≤
      ∑ i ∈ block, n.choose i :=
    Finset.sum_le_sum hterm
  have hsubset : block ⊆ Finset.range (n + 1) := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    simp
    omega
  have hfull : (∑ i ∈ block, n.choose i) ≤
      ∑ i ∈ Finset.range (n + 1), n.choose i := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ _ => by omega)
  have hcard : block.card = n / 2 - k + 1 := by
    dsimp [block]
    rw [Nat.card_Icc]
    omega
  calc
    (n / 2 - k + 1) * n.choose k =
        ∑ i ∈ block, n.choose k := by
      rw [Finset.sum_const, nsmul_eq_mul, hcard]
      norm_num
    _ ≤ ∑ i ∈ block, n.choose i := hsum
    _ ≤ ∑ i ∈ Finset.range (n + 1), n.choose i := hfull
    _ = 2 ^ n := Nat.sum_range_choose n

theorem choose_adjacent_sub_mul_le (n k : Nat) (hk : k ≤ n / 2) :
    (n + 1) * (n.choose k - n.choose (k - 1)) ≤ 4 * 2 ^ n := by
  by_cases hk0 : k = 0
  · subst k
    simp only [Nat.choose_zero_right, Nat.zero_sub, Nat.choose_zero_succ,
      Nat.sub_zero, mul_one]
    have hpow : n + 1 ≤ 2 ^ n := by
      simpa using Nat.choose_succ_le_two_pow n 1
    omega
  let A := n.choose k
  let B := n.choose (k - 1)
  let den := n - k + 1
  let d := n + 1 - 2 * k
  let s := n / 2 - k + 1
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
  have hpred : k - 1 ≤ n / 2 := by omega
  have hBA : B ≤ A := by
    dsimp [A, B]
    exact choose_right_mono_to_middle n (by omega) hk
  have hchoose : A * k = B * den := by
    have h := Nat.choose_succ_right_eq n (k - 1)
    rw [show n - (k - 1) = n - k + 1 by omega] at h
    dsimp [A, B, den]
    simpa [Nat.sub_add_cancel hkpos] using h
  have hdiff : (A - B) * den = A * d := by
    calc
      (A - B) * den = A * den - B * den := Nat.sub_mul A B den
      _ = A * den - A * k := by rw [← hchoose]
      _ = A * (den - k) := (Nat.mul_sub_left_distrib A den k).symm
      _ = A * d := by
        congr 1
        dsimp [den, d]
        omega
  have hblock : s * A ≤ 2 ^ n := by
    dsimp [s, A]
    exact choose_mul_middle_block_le_two_pow n k hk
  have hnum : (n + 1) * d ≤ 4 * den * s := by
    have h1 : n + 1 ≤ 2 * den := by
      dsimp [den]
      omega
    have h2 : d ≤ 2 * s := by
      dsimp [d, s]
      omega
    calc
      (n + 1) * d ≤ (2 * den) * (2 * s) := Nat.mul_le_mul h1 h2
      _ = 4 * den * s := by ring
  have hden : 0 < den := by
    dsimp [den]
    omega
  apply Nat.le_of_mul_le_mul_right _ hden
  calc
    (n + 1) * (n.choose k - n.choose (k - 1)) * den =
        A * ((n + 1) * d) := by
      dsimp [A, B] at hdiff ⊢
      rw [mul_assoc, hdiff]
      ring
    _ ≤ A * (4 * den * s) := Nat.mul_le_mul_left A hnum
    _ = 4 * den * (s * A) := by ring
    _ ≤ 4 * den * 2 ^ n := Nat.mul_le_mul_left (4 * den) hblock
    _ = 4 * 2 ^ n * den := by ring

theorem isingBinomialWeight_sub_pred_le
    (n k : Nat) (hk : k ≤ n / 2) :
    isingBinomialWeight n k - isingBinomialWeightPrev n k ≤
      4 / (n + 1 : Real) := by
  by_cases hk0 : k = 0
  · subst k
    simp only [isingBinomialWeightPrev, if_pos, sub_zero]
    have hpowNat : n + 1 ≤ 2 ^ n := by
      simpa using Nat.choose_succ_le_two_pow n 1
    have hpowReal : (n + 1 : Real) ≤ (2 : Real) ^ n := by exact_mod_cast hpowNat
    unfold isingBinomialWeight
    simp only [Nat.choose_zero_right, Nat.cast_one]
    have hn : (0 : Real) < n + 1 := by positivity
    have hp : (0 : Real) < (2 : Real) ^ n := by positivity
    apply (div_le_div_iff₀ hp hn).2
    nlinarith
  have hBA : n.choose (k - 1) ≤ n.choose k :=
    choose_right_mono_to_middle n (by omega) hk
  have hnat := choose_adjacent_sub_mul_le n k hk
  have hreal : (n + 1 : Real) *
      ((n.choose k : Real) - n.choose (k - 1)) ≤
        4 * (2 : Real) ^ n := by
    exact_mod_cast hnat
  have hn : (0 : Real) < n + 1 := by positivity
  have hpow : (0 : Real) < (2 : Real) ^ n := by positivity
  rw [isingBinomialWeightPrev, if_neg hk0]
  unfold isingBinomialWeight
  apply (le_div_iff₀ hn).2
  calc
    ((n.choose k : Real) / 2 ^ n -
          (n.choose (k - 1) : Real) / 2 ^ n) * (n + 1 : Real) =
      ((n + 1 : Real) *
        ((n.choose k : Real) - n.choose (k - 1))) / 2 ^ n := by ring
    _ ≤ (4 * (2 : Real) ^ n) / 2 ^ n :=
      div_le_div_of_nonneg_right hreal hpow.le
    _ = 4 := by field_simp


theorem isingLineBinomialKernel_adjacentStart_sub_le
    (t : Nat) (x y : Int) (hy : y < x + 1) :
    isingLineBinomialKernel t x y -
        isingLineBinomialKernel t (x + 2) y ≤
      4 / (t + 1 : Real) := by
  by_cases hex : ∃ k ∈ Finset.range (t + 1),
      y = x + 2 * (k : Int) - (t : Int)
  · rcases hex with ⟨k, hkRange, hkEnd⟩
    have hkt : k ≤ t / 2 := by
      push_cast at hkEnd
      omega
    have hlower : isingLineBinomialKernel t x y =
        isingBinomialWeight t k := by
      unfold isingLineBinomialKernel
      rw [Finset.sum_eq_single k]
      · simp [hkEnd]
      · intro b hb hbk
        have hbne : ¬ y = x + 2 * (b : Int) - (t : Int) := by
          intro hbe
          have : b = k := by
            push_cast at hbe hkEnd
            omega
          exact hbk this
        simp [hbne]
      · exact fun hknot => (hknot hkRange).elim
    have hupper : isingLineBinomialKernel t (x + 2) y =
        isingBinomialWeightPrev t k := by
      by_cases hk0 : k = 0
      · subst k
        have hzero : isingLineBinomialKernel t (x + 2) y = 0 := by
          unfold isingLineBinomialKernel
          apply Finset.sum_eq_zero
          intro b hb
          have hbne : ¬ y = x + 2 + 2 * (b : Int) - (t : Int) := by
            intro hbe
            push_cast at hbe hkEnd
            omega
          simp [hbne]
        rw [hzero]
        simp [isingBinomialWeightPrev]
      · have hkPredRange : k - 1 ∈ Finset.range (t + 1) := by
          simp
          omega
        rw [isingBinomialWeightPrev, if_neg hk0]
        unfold isingLineBinomialKernel
        rw [Finset.sum_eq_single (k - 1)]
        · have heq : y = x + 2 + 2 * ((k - 1 : Nat) : Int) - (t : Int) := by
            push_cast at hkEnd ⊢
            omega
          simp [heq]
        · intro b hb hbk
          have hbne : ¬ y = x + 2 + 2 * (b : Int) - (t : Int) := by
            intro hbe
            have : b = k - 1 := by
              push_cast at hbe hkEnd
              omega
            exact hbk this
          simp [hbne]
        · exact fun hknot => (hknot hkPredRange).elim
    rw [hlower, hupper]
    exact isingBinomialWeight_sub_pred_le t k hkt
  · have hlower : isingLineBinomialKernel t x y = 0 := by
      unfold isingLineBinomialKernel
      apply Finset.sum_eq_zero
      intro k hk
      have hkne : ¬ y = x + 2 * (k : Int) - (t : Int) := by
        intro heq
        exact hex ⟨k, hk, heq⟩
      simp [hkne]
    rw [hlower]
    have hupper := isingLineBinomialKernel_nonneg t (x + 2) y
    have hbound : (0 : Real) ≤ 4 / (t + 1 : Real) := by positivity
    linarith

end
end StatMech.Universality
