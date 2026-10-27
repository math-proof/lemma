import Initialize.Tactic.Attr.Basic


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


-- created on 2021-07-06
-- updated on 2026-10-26
