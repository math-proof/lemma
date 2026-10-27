import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Algebra.BigOperators.Ring.Finset
import Initialize.Tactic.Attr.Basic
open Finset Nat


@[path]
private lemma main
-- given
  (n i : ℕ) :
-- imply
  ∑ k ∈ range (n + 1),
      (-1 : ℤ) ^ (k - i) * (stirlingFirst n k : ℤ) * (stirlingSecond k i : ℤ) =
    if n = i then 1 else 0 := by
-- proof
  have signed : ∀ n i,
      ∑ k ∈ range (n + 1),
        (-1 : ℤ) ^ (n - k) * (stirlingFirst n k : ℤ) * (stirlingSecond k i : ℤ) =
      if n = i then 1 else 0 := by
    intro n
    induction n with
    | zero =>
      intro i
      cases i with
      | zero => simp [stirlingFirst_zero, stirlingSecond_zero]
      | succ i => simp [stirlingSecond_zero_succ]
    | succ n ih =>
      intro i
      cases i with
      | zero =>
        rw [sum_range_succ']
        simp [stirlingFirst_succ_zero, stirlingSecond_succ_zero]
      | succ i =>
        rw [sum_range_succ']
        simp only [cast_zero, stirlingSecond_eq_zero_of_lt (succ_pos _), mul_zero]
        have hshift : ∀ j ∈ range (n + 1),
            (-1 : ℤ) ^ ((n + 1) - (j + 1)) *
              (stirlingFirst (n + 1) (j + 1) : ℤ) * (stirlingSecond (j + 1) (i + 1) : ℤ) =
            (-1) ^ (n - j) *
              ((n : ℤ) * stirlingFirst n (j + 1) + stirlingFirst n j) *
              ((i + 1 : ℤ) * stirlingSecond j (i + 1) + stirlingSecond j i) := by
          intro j hj
          have hj : j ≤ n := by simpa [mem_range] using hj
          rw [stirlingFirst_succ_succ, stirlingSecond_succ_succ]
          have hexp : (n + 1) - (j + 1) = n - j := by omega
          rw [hexp]
          push_cast
          ring
        rw [sum_congr rfl hshift]
        simp only [add_zero]
        have hblock : ∀ j,
            (i + 1 : ℤ) * (stirlingSecond j (i + 1) : ℤ) + (stirlingSecond j i : ℤ) =
              (stirlingSecond (j + 1) (i + 1) : ℤ) := by
          intro j
          rw [stirlingSecond_succ_succ]
          push_cast
          ring
        simp_rw [hblock]
        simp_rw [mul_assoc]
        simp_rw [add_mul]
        simp_rw [mul_add, sum_add_distrib]
        have hown : ∑ j ∈ range (n + 1),
            (-1 : ℤ) ^ (n - j) * (stirlingFirst n j : ℤ) * (stirlingSecond (j + 1) (i + 1) : ℤ) =
            (i + 1 : ℤ) * (if n = i + 1 then 1 else 0) + if n = i then 1 else 0 := by
          have hback : ∀ j,
              (stirlingSecond (j + 1) (i + 1) : ℤ) =
                (i + 1 : ℤ) * stirlingSecond j (i + 1) + stirlingSecond j i := by
            intro j
            rw [stirlingSecond_succ_succ]
            push_cast
            ring
          simp_rw [hback]
          have hpull : ∀ x,
              (-1 : ℤ) ^ (n - x) * (stirlingFirst n x : ℤ) *
                ((i + 1 : ℤ) * stirlingSecond x (i + 1) + stirlingSecond x i) =
              (i + 1 : ℤ) * ((-1) ^ (n - x) * stirlingFirst n x * stirlingSecond x (i + 1)) +
                (-1) ^ (n - x) * stirlingFirst n x * stirlingSecond x i := by
            intro x
            ring
          simp_rw [hpull, sum_add_distrib, ← mul_sum]
          simp [ih i, ih (i + 1)]
        have hshiftSum : ∑ j ∈ range (n + 1),
            (-1 : ℤ) ^ (n - j) *
              ((n : ℤ) * (stirlingFirst n (j + 1) : ℤ) * (stirlingSecond (j + 1) (i + 1) : ℤ)) =
            -((n : ℤ) * (if n = i + 1 then 1 else 0)) := by
          have h0 : stirlingFirst n (n + 1) = 0 := stirlingFirst_eq_zero_of_lt (lt_succ_self n)
          have hre : ∀ j ∈ range (n + 1),
              (-1 : ℤ) ^ (n - j) * (stirlingFirst n (j + 1) : ℤ) *
                (stirlingSecond (j + 1) (i + 1) : ℤ) =
              -((-1) ^ (n - (j + 1)) * (stirlingFirst n (j + 1) : ℤ) *
                (stirlingSecond (j + 1) (i + 1) : ℤ)) := by
            intro j hj
            if hjn : j = n then
              simp [hjn, h0]
            else
              have hlt : j < n := lt_of_le_of_ne (by simpa [mem_range] using hj) hjn
              have hexp : n - j = (n - (j + 1)) + 1 := by omega
              rw [hexp, pow_succ]
              ring
          have hfac : ∀ j,
              (-1 : ℤ) ^ (n - j) *
                ((n : ℤ) * (stirlingFirst n (j + 1) : ℤ) * (stirlingSecond (j + 1) (i + 1) : ℤ)) =
              (n : ℤ) * ((-1) ^ (n - j) * stirlingFirst n (j + 1) *
                stirlingSecond (j + 1) (i + 1)) := by
            intro j
            ring
          simp_rw [hfac, ← mul_sum, sum_congr rfl hre, sum_neg_distrib]
          have hpad : ∑ j ∈ range (n + 1),
              (-1 : ℤ) ^ (n - (j + 1)) * (stirlingFirst n (j + 1) : ℤ) *
                (stirlingSecond (j + 1) (i + 1) : ℤ) =
              ∑ k ∈ range (n + 1),
                (-1 : ℤ) ^ (n - k) * (stirlingFirst n k : ℤ) * (stirlingSecond k (i + 1) : ℤ) := by
            rw [sum_range_succ, sum_range_succ']
            simp [h0, stirlingSecond_zero_succ]
          rw [hpad, ih (i + 1)]
          ring
        rw [hshiftSum]
        simp_rw [← mul_assoc]
        rw [hown]
        if h1 : n = i then
          subst h1
          simp
        else if h2 : n = i + 1 then
          subst h2
          simp
        else
          simp [h1, h2]
  have hterm : ∀ k ∈ range (n + 1),
      (-1 : ℤ) ^ (k - i) * (stirlingFirst n k : ℤ) * (stirlingSecond k i : ℤ) =
      (-1) ^ (n - i) *
        ((-1) ^ (n - k) * (stirlingFirst n k : ℤ) * (stirlingSecond k i : ℤ)) := by
    intro k hk
    if hki : i ≤ k then
      have hkn : k ≤ n := by simpa [mem_range] using hk
      have hexp : (n - k) + (n - i) = (k - i) + 2 * (n - k) := by omega
      have hpow : (-1 : ℤ) ^ (k - i) = (-1) ^ ((k - i) + 2 * (n - k)) := by
        rw [pow_add, pow_mul]
        simp
      rw [hpow, ← hexp, pow_add]
      ring
    else
      simp [stirlingSecond_eq_zero_of_lt (lt_of_not_ge hki)]
  rw [sum_congr rfl hterm, ← mul_sum, signed n i]
  split_ifs with h <;> simp [h]


-- created on 2023-08-20
-- updated on 2026-10-26
