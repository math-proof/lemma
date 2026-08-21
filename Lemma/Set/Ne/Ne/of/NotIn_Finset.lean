import sympy.Basic


@[main]
private lemma main
  {e a b : α}
-- given
  (h : e ∉ ({a, b} : Set α)) :
-- imply
  e ≠ a ∧ e ≠ b := by
-- proof
  simp [Set.mem_insert_iff, Set.mem_singleton_iff] at h ⊢
  exact h


-- created on 2018-11-17
-- updated on 2026-08-20
