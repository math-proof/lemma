import sympy.Basic


@[path]
private lemma main
  {m : ℕ}
  {y : ℕ → ℝ}
  {t : ℕ}
-- given
  (h : t ∈ Finset.range m) :
-- imply
  ∑ j ∈ Finset.range m, y j = (∑ j ∈ (Finset.range m).erase t, y j) + y t := by
-- proof
  exact (Finset.sum_erase_add _ _ h).symm


-- created on 2021-03-09
