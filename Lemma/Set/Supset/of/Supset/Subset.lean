import sympy.Basic


@[path]
private lemma main
  {A X B : Set α}
-- given
  (h₀ : X ⊇ A)
  (h₁ : X ⊆ B) :
-- imply
  B ⊇ A :=
-- proof
  h₀.trans h₁


-- created on 2026-10-11
-- updated on 2026-10-17
