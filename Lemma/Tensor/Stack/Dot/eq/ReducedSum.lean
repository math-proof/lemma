import sympy.Basic


@[path]
private lemma main
  {n : ℕ} [NeZero n]
  {x : Fin n → ℝ} :
-- imply
  ∑ k : Fin n, (x k - (∑ i, x i) / (n : ℝ)) = 0 := by
-- proof
  have hn : (n : ℝ) ≠ 0 := by
    exact_mod_cast (NeZero.ne n)
  simp [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  field_simp [hn]
  ring


-- created on 2022-03-16
-- updated on 2026-10-17
