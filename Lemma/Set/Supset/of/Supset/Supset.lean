import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {A X B : Set α}
-- given
  (h₀ : X ⊇ A)
  (h₁ : B ⊇ X) :
-- imply
  B ⊇ A :=
-- proof
  h₀.trans h₁


-- created on 2021-07-09
-- updated on 2026-10-26
