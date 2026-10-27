import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n : ℕ}
  {f : ℕ → ℝ} :
-- imply
  ∑ i ∈ Finset.range n, f (i + 1) = ∑ i ∈ Finset.Ico 1 (n + 1), f i := by
-- proof
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_Ico_succ_top (show 1 ≤ n + 1 by omega)]


-- created on 2018-12-08
-- updated on 2026-10-26
