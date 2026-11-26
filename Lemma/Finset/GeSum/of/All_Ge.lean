import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n : ℕ}
  {f g : ℕ → ℝ}
-- given
  (h : ∀ i < n, f i ≥ g i) :
-- imply
  ∑ i < n, f i ≥ ∑ i < n, g i :=
-- proof
  Finset.sum_le_sum (fun i hi => h i (by simpa using hi))


-- created on 2019-01-13
