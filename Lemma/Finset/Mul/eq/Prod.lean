import sympy.Basic


@[main]
private lemma distribute
  {i n : ℕ}
  {a : ℝ}
  {f : ℕ → ℝ} :
-- imply
  a ^ n * ∏ k ∈ Finset.Ico i (n + i), f k = ∏ k ∈ Finset.Ico i (n + i), (f k * a) := by
-- proof
  rw [Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Ico, show n + i - i = n by omega, mul_comm]


@[main]
private lemma division
  {n : ℕ}
  {f g : ℕ → ℝ} :
-- imply
  (∏ k ∈ Finset.range n, f k) / ∏ k ∈ Finset.range n, g k = ∏ k ∈ Finset.range n, (f k / g k) :=
-- proof
  (Finset.prod_div_distrib f g).symm


@[main]
private lemma limits.push
  [CommMonoid α]
  {i n : ℕ}
  {f : ℕ → α}
-- given
  (h : i ≤ n) :
-- imply
  (∏ k ∈ Finset.Ico i n, f k) * f n = ∏ k ∈ Finset.Ico i (n + 1), f k :=
-- proof
  (Finset.prod_Ico_succ_top h f).symm


-- created on 2026-09-27
