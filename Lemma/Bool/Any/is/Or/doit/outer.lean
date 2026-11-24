import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x : ℕ → ℕ → ℝ}
  {f : ℕ → ℕ} :
-- imply
  ∑ i ∈ Finset.range 2, ∑ j ∈ Finset.range (f i), x i j = ∑ j ∈ Finset.range (f 0), x 0 j + ∑ j ∈ Finset.range (f 1), x 1 j := by
-- proof
  simp [Finset.sum_range_succ]




-- created on 2026-09-27
-- updated on 2026-11-24
