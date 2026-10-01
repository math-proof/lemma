import sympy.Basic


@[main]
private lemma subst
  {a b : α}
  {P : α → Prop} :
-- imply
  a = b ∧ P a ↔ a = b ∧ P b := by
-- proof
  constructor
  ·
    rintro ⟨rfl, h⟩
    exact ⟨rfl, h⟩
  ·
    rintro ⟨rfl, h⟩
    exact ⟨rfl, h⟩


-- created on 2023-08-26
