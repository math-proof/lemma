import sympy.Basic


@[main]
private lemma main
  {α β : Type*}
  {t y : α}
  {P : Prop}
  {f : α → α → β}
  {z : β}
-- given
  (h : t = y ∧ P → f t y = z) :
-- imply
  t = y ∧ P → f y y = z := by
-- proof
  rintro ⟨rfl, hp⟩
  exact h ⟨rfl, hp⟩


-- created on 2026-10-03
