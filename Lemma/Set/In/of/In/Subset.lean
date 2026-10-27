import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x : α}
  {A B : Set α}
-- given
  (h₀ : A ⊆ B)
  (h₁ : x ∈ A) :
-- imply
  x ∈ B :=
-- proof
  h₀ h₁


-- created on 2018-01-12
-- updated on 2026-10-26
