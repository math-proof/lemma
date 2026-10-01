import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℕ} :
-- imply
  ∑ k ∈ Finset.range n, k ^ 3 = (∑ k ∈ Finset.range n, k) ^ 2 := by
-- proof
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    have h := Finset.sum_range_id_mul_two n
    generalize (∑ i ∈ Finset.range n, i) = S at h ⊢
    cases n with
    | zero =>
      simp at h
      simp [h]
    | succ m =>
      simp only [Nat.add_sub_cancel] at h
      zify at h ⊢
      linear_combination (-((m : ℤ) + 1)) * h


-- created on 2023-12-13
