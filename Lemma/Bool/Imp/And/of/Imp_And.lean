import sympy.Basic


@[main]
private lemma subst
  {p : Prop}
  {a b : α}
  {P : α → Prop}
-- given
  (h : a = b ∧ p → P a) :
-- imply
  a = b ∧ p → P b := by
-- proof
  intro hab
  rw [← hab.1]
  exact h hab


-- created on 2026-09-27
