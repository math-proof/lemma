import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x y : ℝ}
  {m : ℕ} :
-- imply
  (x + y) ^ m = ∑ k ∈ Finset.range (m + 1), x ^ k * y ^ (m - k) * (Nat.choose m k : ℝ) :=
-- proof
  add_pow x y m


-- created on 2022-01-15
-- updated on 2026-10-26
