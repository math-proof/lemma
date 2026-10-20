import sympy.Basic


@[path]
private lemma main
  {n d a : ℕ}
  {f : ℕ → ℝ}
  {g : ℕ → ℕ → ℝ} :
-- imply
  ∑ j ∈ Finset.Ico a (n - d), ∑ i ∈ Finset.Ico (j + d) n, f i * g i j =
    ∑ i ∈ Finset.Ico (a + d) n, ∑ j ∈ Finset.Ico a (i - d + 1), f i * g i j := by
-- proof
  apply Finset.sum_comm'
  intro j i
  simp only [Finset.mem_Ico]
  omega


-- created on 2019-11-08
-- updated on 2026-10-12
