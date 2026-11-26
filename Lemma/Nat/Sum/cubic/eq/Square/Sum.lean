import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n : ℕ} :
-- imply
  ∑ k < n, k ^ 3 = (∑ k < n, k) ^ 2 := by
-- proof
  try simp only [Nat.Iio_eq_range] at *
  induction n with
  | zero => simp
  | succ n ih =>
    try simp only [Nat.Iio_eq_range] at *
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    have h := Finset.sum_range_id_mul_two n
    generalize (∑ i < n, i) = S at h ⊢
    cases n with
    | zero =>
      try simp only [Nat.Iio_eq_range] at *
      simp at h
      simp []
    | succ m =>
      try simp only [Nat.Iio_eq_range] at *
      simp only [Nat.add_sub_cancel] at h
      zify at h ⊢
      linear_combination (-((m : ℤ) + 1)) * h


-- created on 2023-12-13
