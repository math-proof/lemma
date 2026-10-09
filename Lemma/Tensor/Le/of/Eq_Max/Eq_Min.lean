import sympy.Basic


@[path]
private lemma main
  {n l u d i : ℤ}
  {β ζ : ℤ → ℤ}
-- given
  (h₀ : d > 0)
  (h₁ : ∀ i, β i = max (i - l + 1) ((i - l + 1) % d))
  (h₂ : ∀ i, ζ i = min (i + u) n) :
-- imply
  ζ i - β i ≤ min n (l + u - 1) := by
-- proof
  have h := Int.emod_nonneg (i - l + 1) (ne_of_gt h₀)
  rw [h₁, h₂]
  simp only [min_def, max_def]
  split_ifs <;> omega


-- created on 2021-12-26
