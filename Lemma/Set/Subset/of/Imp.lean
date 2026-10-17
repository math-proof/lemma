import sympy.Basic


@[path]
private lemma main
  {A B : Set α}
-- given
  (h : ∀ x, x ∈ A → x ∈ B) :
-- imply
  A ⊆ B :=
-- proof
  h


-- created on 2021-04-25
-- updated on 2026-10-17
