import sympy.Basic


@[main]
private lemma main
  {x a b d : ℝ}
-- given
  (hd : d ≠ 0)
  (h : x ∈ ({a, b} : Set ℝ)) :
-- imply
  x * d ∈ ({a * d, b * d} : Set ℝ) := by
-- proof
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h ⊢
  obtain h | h := h
  · left
    rw [h]
  · right
    rw [h]


-- created on 2023-05-30
