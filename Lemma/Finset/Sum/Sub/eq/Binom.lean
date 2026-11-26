import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n : ℕ} :
-- imply
  ∑ i < n, ∑ j < i, ((i : ℤ) - j) = ((n + 1).choose 3 : ℤ) := by
-- proof
  simp only [Nat.Iio_eq_range]
  have inner : ∀ m : ℕ, (Finset.range m).sum (fun j => (m : ℤ) - j) = ((m + 1).choose 2 : ℤ) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have e : ∀ j < m, ((↑(m + 1) : ℤ) - j) = (m : ℤ) - j + 1 := fun j _ => by push_cast; ring
      try simp only [← Finset.mem_range] at *
      rw [Finset.sum_range_succ, Finset.sum_congr rfl e, Finset.sum_add_distrib, ih, Nat.choose_succ_succ (m + 1) 1,
        Nat.choose_one_right]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      push_cast
      ring
  induction n with
  | zero =>
    rw [Nat.choose_eq_zero_of_lt (by norm_num)]
    simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, inner, Nat.choose_succ_succ (n + 1) 2]
    push_cast
    ring


-- created on 2023-10-21
-- updated on 2026-11-26
