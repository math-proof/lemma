import sympy.Basic


@[main]
private lemma main
  [DecidableEq α]
  {s : Finset α}
  {f : α → ℝ}
  {e : α}
-- given
  (h : e ∉ s) :
-- imply
  ∑ x ∈ insert e s, f x = ∑ x ∈ s, f x + f e := by
-- proof
  exact (Finset.sum_insert h).trans (add_comm _ _)


-- created on 2021-03-17
