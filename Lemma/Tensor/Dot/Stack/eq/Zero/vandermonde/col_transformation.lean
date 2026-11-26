import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x y : ℝ}
  {m : ℕ} :
-- imply
  (x + y) ^ m = ∑ k < (m + 1), x ^ k * y ^ (m - k) * (Nat.choose m k : ℝ) :=
-- proof
  (Nat.Iio_eq_range (m + 1)).symm ▸ add_pow x y m


-- created on 2021-11-30
-- updated on 2026-10-26
