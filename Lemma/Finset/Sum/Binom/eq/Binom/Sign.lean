import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n t : ℕ} :
-- imply
  ∑ i < n, ∑ j < i, ((i - j).choose t : ℤ) = ((n + (t : ℤ).sign.toNat).choose (t + 2) : ℤ) := by
-- proof
  simp only [Nat.Iio_eq_range]
  have inner : ∀ i : ℕ, (Finset.range i).sum (fun j => ((i - j).choose t : ℤ)) = ((i + 1).choose (t + 1) : ℤ) - if t = 0 then 1 else 0 := by
    intro i
    induction i with
    | zero =>
      obtain rfl | ht := Nat.eq_zero_or_pos t
      · simp
      ·
        rw [ite_eq_right (by omega), Nat.choose_eq_zero_of_lt (by omega)]
        simp
    | succ i ih =>
      rw [Finset.sum_range_succ']
      simp only [Nat.add_sub_add_right, Nat.sub_zero]
      rw [ih, Nat.choose_succ_succ (i + 1) t]
      push_cast
      ring
  have outer : ∀ n : ℕ, (Finset.range n).sum (fun i => (Finset.range i).sum (fun j => ((i - j).choose t : ℤ))) =
      ((n + 1).choose (t + 2) : ℤ) - n * if t = 0 then 1 else 0 := by
    intro n
    induction n with
    | zero =>
      rw [Nat.choose_eq_zero_of_lt (by omega)]
      simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, inner, Nat.choose_succ_succ (n + 1) (t + 1)]
      push_cast
      ring
  rw [outer]
  obtain rfl | ht := Nat.eq_zero_or_pos t
  ·
    simp only [Int.sign_zero, Int.toNat_zero, add_zero, Nat.cast_zero]
    obtain rfl | hn := Nat.eq_zero_or_pos n
    · simp
    ·
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      rw [Nat.choose_succ_succ (m + 1) 1, Nat.choose_one_right]
      push_cast
      ring
  ·
    rw [ite_eq_right (by omega), mul_zero, sub_zero, Int.sign_natCast_of_ne_zero (by omega)]
    rfl


-- created on 2023-10-22
-- updated on 2026-11-26
