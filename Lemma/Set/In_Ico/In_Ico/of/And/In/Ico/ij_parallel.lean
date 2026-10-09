import sympy.Basic


@[path]
private lemma main
  {i j a m d n : ℤ}
-- given
  (h₀ : i ∈ Set.Ico (d + j) (n + j))
  (h₁ : j ∈ Set.Ico a m) :
-- imply
  i ∈ Set.Ico (d + a) (n + m - 1) ∧ j ∈ Set.Ico (max a (i - n + 1)) (min m (i - d + 1)) := by
-- proof
  simp only [Set.mem_Ico, max_le_iff, lt_min_iff] at h₀ h₁ ⊢
  omega


-- created on 2020-03-21
