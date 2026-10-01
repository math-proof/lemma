import sympy.Basic


@[main]
private lemma main
  {p q : Prop}
-- given
  (h : p → q)
  (r : Prop):
-- imply
  r ∧ p → q := by
-- proof
  intro ⟨hr, hp⟩
  exact h hp


@[main]
private lemma Cond
  {p q c : Prop}
-- given
  (h₀ : c)
  (h₁ : p → q) :
-- imply
  p ∧ c → q := by
-- proof
  intro hpc
  have _ := h₀
  exact h₁ hpc.1


-- created on 2018-10-12
-- updated on 2025-10-01
-- updated on 2026-09-27
