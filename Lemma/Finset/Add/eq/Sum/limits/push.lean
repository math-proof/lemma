import sympy.Basic


@[path]
private lemma main
  [AddCommMonoid α]
  {f : ℕ → α}
  {i n : ℕ}
-- given
  (h : i ≤ n) :
-- imply
  ∑ k ∈ Finset.Ico i n, f k + f n = ∑ k ∈ Finset.Ico i (n + 1), f k := by
-- proof
  have hio : Finset.Ico i (n + 1) = insert n (Finset.Ico i n) :=
    Nat.Ico_succ_right_eq_insert_Ico h
  rw [hio, Finset.sum_insert (by simp)]
  exact add_comm _ _


-- created on 2018-08-08
