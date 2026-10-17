import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  {π R : Fin n → ℝ}
-- given
  (h₀ : ∀ a, π a ≠ 0) :
-- imply
  ∑ a, π a * ((1 / π a) * R a) = ∑ a, R a := by
-- proof
  refine Finset.sum_congr rfl ?_
  intro a _
  have hπ : π a ≠ 0 := h₀ a
  field_simp [hπ]


-- created on 2026-10-11
-- updated on 2026-10-17
