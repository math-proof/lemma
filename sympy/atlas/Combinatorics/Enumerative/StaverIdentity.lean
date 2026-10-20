/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/StaverIdentity.lean -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace MetaMathlibExt

/-- Sign split: `(-1)^(n-k) * (-1)^k = (-1)^n` for `k ≤ n`. -/
theorem staver_sign_mul (n k : ℕ) (hk : k ≤ n) :
    (-1 : ℚ) ^ (n - k) * (-1 : ℚ) ^ k = (-1 : ℚ) ^ n := by
  rw [← pow_add, Nat.sub_add_cancel hk]

/-- Square of a signed power is one. -/
theorem staver_sign_sq (k : ℕ) : (-1 : ℚ) ^ k * (-1 : ℚ) ^ k = 1 := by
  rw [← pow_add]
  exact Even.neg_one_pow ⟨k, rfl⟩

/-- For odd `n`, reflection flips the sign. -/
theorem staver_sign_odd {n k : ℕ} (hodd : Odd n) (hk : k ≤ n) :
    (-1 : ℚ) ^ (n - k) = -(-1 : ℚ) ^ k := by
  have hmul := staver_sign_mul n k hk
  have hsq := staver_sign_sq k
  have he1 : (-1 : ℚ) ^ n = -1 := hodd.neg_one_pow
  calc (-1 : ℚ) ^ (n - k) = (-1 : ℚ) ^ (n - k) * 1 := (mul_one _).symm
    _ = (-1 : ℚ) ^ (n - k) * ((-1 : ℚ) ^ k * (-1 : ℚ) ^ k) := by rw [hsq]
    _ = ((-1 : ℚ) ^ (n - k) * (-1 : ℚ) ^ k) * (-1 : ℚ) ^ k := by ring
    _ = (-1 : ℚ) ^ n * (-1 : ℚ) ^ k := by rw [hmul]
    _ = -(-1 : ℚ) ^ k := by rw [he1, neg_one_mul]

/-- For even `n`, reflection preserves the sign. -/
theorem staver_sign_even {n k : ℕ} (heven : Even n) (hk : k ≤ n) :
    (-1 : ℚ) ^ (n - k) = (-1 : ℚ) ^ k := by
  have hmul := staver_sign_mul n k hk
  have hsq := staver_sign_sq k
  have he1 : (-1 : ℚ) ^ n = 1 := heven.neg_one_pow
  calc (-1 : ℚ) ^ (n - k) = (-1 : ℚ) ^ (n - k) * 1 := (mul_one _).symm
    _ = (-1 : ℚ) ^ (n - k) * ((-1 : ℚ) ^ k * (-1 : ℚ) ^ k) := by rw [hsq]
    _ = ((-1 : ℚ) ^ (n - k) * (-1 : ℚ) ^ k) * (-1 : ℚ) ^ k := by ring
    _ = (-1 : ℚ) ^ n * (-1 : ℚ) ^ k := by rw [hmul]
    _ = (-1 : ℚ) ^ k := by rw [he1, one_mul]

/-- Reflection `k ↦ n - k` preserves the unweighted reciprocal-binomial sum. -/
theorem staver_reflect_zero (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      (-1 : ℚ) ^ (n - k) * ((Nat.choose n k : ℚ))⁻¹) =
    ∑ k ∈ Finset.range (n + 1),
      (-1 : ℚ) ^ k * ((Nat.choose n k : ℚ))⁻¹ := by
  rw [← Finset.sum_range_reflect
    (fun k => (-1 : ℚ) ^ (n - k) * ((Nat.choose n k : ℚ))⁻¹) (n + 1)]
  apply Finset.sum_congr rfl
  intro k hk
  have hkle : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have e1 : n + 1 - 1 - k = n - k := by omega
  have e2 : n - (n - k) = k := by omega
  have e3 : Nat.choose n (n - k) = Nat.choose n k := Nat.choose_symm hkle
  rw [e1, e2, e3]

/-- Reflection for the first-weighted sum, keeping the weight in `ℕ`. -/
theorem staver_reflect_one (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      (-1 : ℚ) ^ (n - k) * (k : ℚ) * ((Nat.choose n k : ℚ))⁻¹) =
    ∑ k ∈ Finset.range (n + 1),
      (-1 : ℚ) ^ k * ((n - k : ℕ) : ℚ) * ((Nat.choose n k : ℚ))⁻¹ := by
  rw [← Finset.sum_range_reflect
    (fun k => (-1 : ℚ) ^ (n - k) * (k : ℚ) * ((Nat.choose n k : ℚ))⁻¹) (n + 1)]
  apply Finset.sum_congr rfl
  intro k hk
  have hkle : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have e1 : n + 1 - 1 - k = n - k := by omega
  have e2 : n - (n - k) = k := by omega
  have e3 : Nat.choose n (n - k) = Nat.choose n k := Nat.choose_symm hkle
  rw [e1, e2, e3]

/-- Staver's identity: for even `n`, `S¹ = (n/2) * S⁰`, and for odd `n`,
`S⁰ = 0`, where `Sᵐ = ∑_{k=0}^n (-1)^{n-k} k^m C(n,k)⁻¹`.

Source: Renzo Sprugnoli, "Alternating Weighted Sums of Inverses of Binomial
Coefficients," Journal of Integer Sequences 15 (2012), Article 12.6.3
(Staver's identity),
<https://cs.uwaterloo.ca/journals/JIS/VOL15/Sprugnoli/sprugnoli6.tex>.
Both parts follow by pairing `k ↔ n - k`: for odd `n`
the pairs cancel, for even `n` they average to `n/2`.
Proves `Wanted` entry `staver_identity`. -/
theorem staver_identity (n : ℕ) :
    (Even n →
      ∑ k ∈ Finset.range (n + 1), (-1 : ℚ) ^ (n - k) * (k : ℚ) * ((Nat.choose n k : ℚ))⁻¹ =
        (n : ℚ) / 2 * ∑ k ∈ Finset.range (n + 1), (-1 : ℚ) ^ (n - k) * ((Nat.choose n k : ℚ))⁻¹) ∧
    (Odd n →
      ∑ k ∈ Finset.range (n + 1), (-1 : ℚ) ^ (n - k) * ((Nat.choose n k : ℚ))⁻¹ = 0) := by
  constructor
  · intro heven
    -- double the weighted sum and pair up
    have h2 : 2 * (∑ k ∈ Finset.range (n + 1),
          (-1 : ℚ) ^ (n - k) * (k : ℚ) * ((Nat.choose n k : ℚ))⁻¹) =
        ∑ k ∈ Finset.range (n + 1),
          (-1 : ℚ) ^ k * (n : ℚ) * ((Nat.choose n k : ℚ))⁻¹ := by
      have hexpand : 2 * (∑ k ∈ Finset.range (n + 1),
            (-1 : ℚ) ^ (n - k) * (k : ℚ) * ((Nat.choose n k : ℚ))⁻¹) =
          ∑ k ∈ Finset.range (n + 1),
            (((-1 : ℚ) ^ (n - k) * (k : ℚ) +
              (-1 : ℚ) ^ k * ((n - k : ℕ) : ℚ)) *
              ((Nat.choose n k : ℚ))⁻¹) := by
        rw [two_mul]
        nth_rewrite 2 [staver_reflect_one]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        ring
      rw [hexpand]
      apply Finset.sum_congr rfl
      intro k hk
      have hkle : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      have hkn : (k : ℚ) + ((n - k : ℕ) : ℚ) = (n : ℚ) := by
        exact_mod_cast Nat.add_sub_cancel' hkle
      rw [staver_sign_even heven hkle]
      linear_combination ((-1 : ℚ) ^ k * ((Nat.choose n k : ℚ))⁻¹) * hkn
    -- double the scaled unweighted sum to the same target
    have h0 : 2 * ((n : ℚ) / 2 * (∑ k ∈ Finset.range (n + 1),
          (-1 : ℚ) ^ (n - k) * ((Nat.choose n k : ℚ))⁻¹)) =
        ∑ k ∈ Finset.range (n + 1),
          (-1 : ℚ) ^ k * (n : ℚ) * ((Nat.choose n k : ℚ))⁻¹ := by
      have hmul : 2 * ((n : ℚ) / 2 * (∑ k ∈ Finset.range (n + 1),
            (-1 : ℚ) ^ (n - k) * ((Nat.choose n k : ℚ))⁻¹)) =
          2 * ∑ k ∈ Finset.range (n + 1),
            ((n : ℚ) / 2 * ((-1 : ℚ) ^ (n - k) *
              ((Nat.choose n k : ℚ))⁻¹)) := by
        congr 1
        exact Finset.mul_sum _ _ _
      rw [hmul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hkle : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      rw [staver_sign_even heven hkle]
      ring
    have hdone : 2 * (∑ k ∈ Finset.range (n + 1),
          (-1 : ℚ) ^ (n - k) * (k : ℚ) * ((Nat.choose n k : ℚ))⁻¹) =
        2 * ((n : ℚ) / 2 * (∑ k ∈ Finset.range (n + 1),
          (-1 : ℚ) ^ (n - k) * ((Nat.choose n k : ℚ))⁻¹)) := by
      linarith [h2, h0]
    exact mul_left_cancel₀ (by norm_num : (2 : ℚ) ≠ 0) hdone
  · intro hodd
    have h2 : 2 * (∑ k ∈ Finset.range (n + 1),
          (-1 : ℚ) ^ (n - k) * ((Nat.choose n k : ℚ))⁻¹) =
        ∑ k ∈ Finset.range (n + 1),
          (((-1 : ℚ) ^ (n - k) + (-1 : ℚ) ^ k) *
            ((Nat.choose n k : ℚ))⁻¹) := by
      rw [two_mul]
      nth_rewrite 2 [staver_reflect_zero]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring
    have hterm : ∀ k ∈ Finset.range (n + 1),
        (((-1 : ℚ) ^ (n - k) + (-1 : ℚ) ^ k) *
          ((Nat.choose n k : ℚ))⁻¹) = 0 := by
      intro k hk
      have hkle : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      rw [staver_sign_odd hodd hkle, neg_add_cancel, zero_mul]
    have hS : 2 * (∑ k ∈ Finset.range (n + 1),
        (-1 : ℚ) ^ (n - k) * ((Nat.choose n k : ℚ))⁻¹) = 0 := by
      rw [h2]
      exact Finset.sum_eq_zero hterm
    linarith

end MetaMathlibExt
