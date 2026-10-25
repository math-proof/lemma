/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRegularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalEnergy
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialPatch.Part15
import Mathlib.Data.Nat.Choose.Vandermonde
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRegularity.Part3


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

open Finset


theorem isingBinomialWeight_sq_sum (n : Nat) :
    ∑ k ∈ range (n + 1), isingBinomialWeight n k ^ 2 =
      (Nat.centralBinom n : Real) / 4 ^ n := by
  have h := Nat.sum_range_choose_sq n
  have hR : (∑ k ∈ range (n + 1), (n.choose k : Real) ^ 2) =
      (Nat.centralBinom n : Real) := by
    exact_mod_cast h
  unfold isingBinomialWeight
  simp_rw [div_pow, ← Finset.sum_div]
  rw [hR]
  congr 1
  rw [show (4 : Real) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul,
    Nat.mul_comm n 2]

theorem ising_sum_choose_adjacent (n : Nat) :
    ∑ k ∈ range (n + 2),
        n.choose k * (if k = 0 then 0 else n.choose (k - 1)) =
      (2 * n).choose (n + 1) := by
  rw [two_mul, Nat.add_choose_eq,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k < n + 2 := Finset.mem_range.mp hk
  by_cases hk0 : k = 0
  · subst k
    simp
  · rw [if_neg hk0]
    congr 1
    symm
    rw [← Nat.choose_symm (by omega : n + 1 - k ≤ n)]
    congr 1
    omega


theorem isingBinomialWeight_diff_sq_sum (n : Nat) :
    ∑ k ∈ range (n + 2),
        (isingBinomialWeight n k - isingBinomialWeightPrev n k) ^ 2 =
      2 * (Nat.centralBinom n : Real) / ((n + 1) * 4 ^ n) := by
  have hA : (∑ k ∈ range (n + 2), isingBinomialWeight n k ^ 2) =
      (Nat.centralBinom n : Real) / 4 ^ n := by
    rw [Finset.sum_range_succ, isingBinomialWeight_sq_sum]
    simp [isingBinomialWeight]
  have hB : (∑ k ∈ range (n + 2), isingBinomialWeightPrev n k ^ 2) =
      (Nat.centralBinom n : Real) / 4 ^ n := by
    rw [Finset.sum_range_succ']
    simpa [isingBinomialWeightPrev] using isingBinomialWeight_sq_sum n
  have hCrossNat := ising_sum_choose_adjacent n
  have hCrossCast :
      (∑ k ∈ range (n + 2),
        (n.choose k : Real) *
          (if k = 0 then 0 else (n.choose (k - 1) : Real))) =
        ((2 * n).choose (n + 1) : Real) := by
    exact_mod_cast hCrossNat
  have hCross : (∑ k ∈ range (n + 2),
      isingBinomialWeight n k * isingBinomialWeightPrev n k) =
      ((2 * n).choose (n + 1) : Real) / 4 ^ n := by
    calc
      _ = ∑ k ∈ range (n + 2),
          ((n.choose k : Real) *
            (if k = 0 then 0 else (n.choose (k - 1) : Real))) / 4 ^ n := by
            apply Finset.sum_congr rfl
            intro k hk
            by_cases hk0 : k = 0
            · subst k
              simp [isingBinomialWeight, isingBinomialWeightPrev]
            simp only [isingBinomialWeightPrev, hk0, if_false,
              isingBinomialWeight]
            rw [div_mul_div_comm]
            congr 1
            rw [show (4 : Real) ^ n = 2 ^ (2 * n) by
              rw [show (4 : Real) = 2 ^ 2 by norm_num, ← pow_mul]]
            rw [← pow_add]
            congr 1
            omega
      _ = (∑ k ∈ range (n + 2),
          (n.choose k : Real) *
            (if k = 0 then 0 else (n.choose (k - 1) : Real))) / 4 ^ n := by
            rw [Finset.sum_div]
      _ = _ := by rw [hCrossCast]
  have hchooseNat := Nat.choose_succ_right_eq (n := 2 * n) (k := n)
  rw [show 2 * n - n = n by omega] at hchooseNat
  have hchoose :
      ((n + 1 : Nat) : Real) * ((2 * n).choose (n + 1) : Real) =
        (n : Real) * (Nat.centralBinom n : Real) := by
    have hchooseRaw :
        (((n + 1) * (2 * n).choose (n + 1) : Nat) : Real) =
          ((n * (2 * n).choose n : Nat) : Real) := by
      exact_mod_cast (by simpa [mul_comm] using hchooseNat)
    simpa [Nat.centralBinom, mul_comm] using hchooseRaw
  have hchoose' :
      ((n : Real) + 1) * ((2 * n).choose (n + 1) : Real) =
        (n : Real) * (Nat.centralBinom n : Real) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hchoose
  have hdiff :
      ((Nat.centralBinom n : Real) - ((2 * n).choose (n + 1) : Real)) *
          (n + 1) = (Nat.centralBinom n : Real) := by
    calc
      _ = (Nat.centralBinom n : Real) * (n + 1) -
          (n + 1) * ((2 * n).choose (n + 1) : Real) := by ring
      _ = (Nat.centralBinom n : Real) * (n + 1) -
          (n : Real) * Nat.centralBinom n := by rw [hchoose']
      _ = _ := by ring
  calc
    _ = ∑ k ∈ range (n + 2),
        (isingBinomialWeight n k ^ 2 + isingBinomialWeightPrev n k ^ 2 -
          2 * (isingBinomialWeight n k * isingBinomialWeightPrev n k)) := by
          apply Finset.sum_congr rfl
          intro k hk
          ring
    _ = (∑ k ∈ range (n + 2), isingBinomialWeight n k ^ 2) +
          (∑ k ∈ range (n + 2), isingBinomialWeightPrev n k ^ 2) -
          2 * (∑ k ∈ range (n + 2),
            isingBinomialWeight n k * isingBinomialWeightPrev n k) := by
          simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
            Finset.mul_sum]
    _ = 2 * (Nat.centralBinom n : Real) / 4 ^ n -
          2 * (((2 * n).choose (n + 1) : Real) / 4 ^ n) := by
          rw [hA, hB, hCross]
          ring
    _ = _ := by
      have hn : (n + 1 : Real) ≠ 0 := by positivity
      have hp : (4 : Real) ^ n ≠ 0 := by positivity
      field_simp
      nlinarith [hdiff]


theorem isingBinomialKernel_gradient_sq_sum_le (n : Nat) :
    (∑ a ∈ range (n + 2), ∑ b ∈ range (n + 1),
      ((isingBinomialWeight n a - isingBinomialWeightPrev n a) *
        isingBinomialWeight n b) ^ 2) ≤
        2 / ((n + 1 : Real) ^ 2) := by
  have hfactor :
      (∑ a ∈ range (n + 2), ∑ b ∈ range (n + 1),
        ((isingBinomialWeight n a - isingBinomialWeightPrev n a) *
          isingBinomialWeight n b) ^ 2) =
      (∑ a ∈ range (n + 2),
          (isingBinomialWeight n a - isingBinomialWeightPrev n a) ^ 2) *
        (∑ b ∈ range (n + 1), isingBinomialWeight n b ^ 2) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    ring
  rw [hfactor, isingBinomialWeight_diff_sq_sum,
    isingBinomialWeight_sq_sum]
  have hc := isingCentralBinom_sq_mul_le n
  have hpow : (16 : Real) ^ n = 4 ^ (n * 2) := by
    rw [show (16 : Real) = 4 ^ 2 by norm_num, ← pow_mul,
      Nat.mul_comm 2 n]
  calc
    2 * (Nat.centralBinom n : Real) / ((n + 1) * 4 ^ n) *
          ((Nat.centralBinom n : Real) / 4 ^ n) =
        2 * ((Nat.centralBinom n : Real) ^ 2 * (2 * n + 1)) /
          (((n + 1 : Real) * (2 * n + 1)) * (16 : Real) ^ n) := by
            field_simp
            rw [hpow]
            ring
    _ ≤ 2 * (16 : Real) ^ n /
          (((n + 1 : Real) * (2 * n + 1)) * (16 : Real) ^ n) := by
            gcongr
    _ = 2 / ((n + 1 : Real) * (2 * n + 1)) := by field_simp
    _ ≤ 2 / ((n + 1 : Real) ^ 2) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      have hn : (0 : Real) ≤ n := by positivity
      nlinarith


theorem isingComplex_normSq_sum_mul_le {ι : Type} (s : Finset ι)
    (c : ι → Real) (z : ι → Complex) :
    Complex.normSq (∑ x ∈ s, (c x : Complex) * z x) ≤
      (∑ x ∈ s, c x ^ 2) * (∑ x ∈ s, Complex.normSq (z x)) := by
  rw [Complex.normSq_eq_norm_sq]
  have hnorm : ‖∑ x ∈ s, (c x : Complex) * z x‖ ≤
      ∑ x ∈ s, |c x| * ‖z x‖ := by
    calc
      _ ≤ ∑ x ∈ s, ‖(c x : Complex) * z x‖ := norm_sum_le _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ (∑ x ∈ s, |c x| * ‖z x‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun x hx ↦
        mul_nonneg (abs_nonneg _) (norm_nonneg _))).mpr hnorm
    _ ≤ (∑ x ∈ s, |c x| ^ 2) * (∑ x ∈ s, ‖z x‖ ^ 2) :=
      Finset.sum_mul_sq_le_sq_mul_sq s (fun x ↦ |c x|) (fun x ↦ ‖z x‖)
    _ = _ := by
      simp only [sq_abs, Complex.normSq_eq_norm_sq]


theorem isingBinomialMean_normSq_sub_le
    (F : Nat → Nat → Complex) (t x y : Nat) (E : Real)
    (left right : Complex)
    (hleft : left = ∑ a ∈ range (t + 2), ∑ b ∈ range (t + 1),
      ((isingBinomialWeight t a * isingBinomialWeight t b : Real) : Complex) *
        F (x + 2 * a) (y + 2 * b))
    (hright : right = ∑ a ∈ range (t + 2), ∑ b ∈ range (t + 1),
      ((isingBinomialWeightPrev t a * isingBinomialWeight t b : Real) : Complex) *
        F (x + 2 * a) (y + 2 * b))
    (hL2 : (∑ a ∈ range (t + 2), ∑ b ∈ range (t + 1),
      Complex.normSq (F (x + 2 * a) (y + 2 * b))) ≤ E) :
    Complex.normSq (left - right) ≤ 2 * E / (t + 1 : Real) ^ 2 := by
  rw [hleft, hright, ← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib, ← sub_mul]
  push_cast
  let s := (range (t + 2)).product (range (t + 1))
  let c : Nat × Nat → Real := fun p ↦
    (isingBinomialWeight t p.1 - isingBinomialWeightPrev t p.1) *
      isingBinomialWeight t p.2
  let z : Nat × Nat → Complex := fun p ↦
    F (x + 2 * p.1) (y + 2 * p.2)
  have hcoeff (a b : Nat) :
      (isingBinomialWeight t a : Complex) *
          (isingBinomialWeight t b : Complex) -
        (isingBinomialWeightPrev t a : Complex) *
          (isingBinomialWeight t b : Complex) = (c (a, b) : Complex) := by
    dsimp [c]
    push_cast
    ring
  simp_rw [hcoeff]
  change Complex.normSq (∑ a ∈ range (t + 2),
      ∑ b ∈ range (t + 1), (c (a, b) : Complex) * z (a, b)) ≤ _
  rw [← Finset.sum_product']
  have hcs := isingComplex_normSq_sum_mul_le s c z
  calc
    Complex.normSq (∑ p ∈ s, (c p : Complex) * z p) ≤
        (∑ p ∈ s, c p ^ 2) * (∑ p ∈ s, Complex.normSq (z p)) := hcs
    _ ≤ (2 / (t + 1 : Real) ^ 2) * E := by
      apply mul_le_mul (by
          simpa [s, c, Finset.sum_product] using
            isingBinomialKernel_gradient_sq_sum_le t)
        (by simpa [s, z, Finset.sum_product] using hL2)
        (Finset.sum_nonneg fun p hp ↦ Complex.normSq_nonneg _)
        (by positivity)
    _ = _ := by ring

end
end StatMech.Universality
