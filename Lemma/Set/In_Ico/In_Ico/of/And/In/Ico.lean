import sympy.Basic


@[path]
private lemma ij_parallel
  {i j a m d n : ℤ}
-- given
  (_h₀ : i ∈ Set.Ico (d + a) (n + m - 1))
  (h₁ : j ∈ Set.Ico (max a (i - n + 1)) (min m (i - d + 1))) :
-- imply
  i ∈ Set.Ico (d + j) (n + j) ∧ j ∈ Set.Ico a m := by
-- proof
  simp only [Set.mem_Ico, max_le_iff, lt_min_iff] at h₁ ⊢
  omega


-- created on 2020-03-21
