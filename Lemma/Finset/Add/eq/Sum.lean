import sympy.Basic


@[main]
private lemma limits.push
  [AddCommMonoid α]
  {i n : ℕ}
  {f : ℕ → α}
-- given
  (h : i ≤ n) :
-- imply
  ∑ k ∈ Finset.Ico i n, f k + f n = ∑ k ∈ Finset.Ico i (n + 1), f k :=
-- proof
  (Finset.sum_Ico_succ_top h f).symm


@[main]
private lemma limits.unshift
  [AddCommMonoid α]
  {i n : ℕ}
  {f : ℕ → α}
-- given
  (h : i < n) :
-- imply
  ∑ k ∈ Finset.Ico (i + 1) n, f k + f i = ∑ k ∈ Finset.Ico i n, f k := by
-- proof
  rw [Finset.sum_eq_sum_Ico_succ_bot h, add_comm]


-- created on 2026-09-27
