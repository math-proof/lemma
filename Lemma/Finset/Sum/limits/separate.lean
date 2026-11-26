import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  [NonUnitalNonAssocSemiring α]
  {n : ℕ}
  {f : ℕ → α}
  {g : ℕ → ℕ → α} :
-- imply
  ∑ p ∈ Finset.range n ×ˢ Finset.range n, f p.2 * g p.1 p.2 =
    ∑ i < n, ∑ j < n, f j * g i j := by
-- proof
  simp only [Nat.Iio_eq_range]
  apply Finset.sum_product


-- created on 2026-10-11
