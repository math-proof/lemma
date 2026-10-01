import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {x : Fin n → ℝ} :
-- imply
  ∑ i, x i * x i = √(∑ i, |x i| ^ 2) ^ 2 := by
-- proof
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sq_abs, sq]


-- created on 2023-06-29
