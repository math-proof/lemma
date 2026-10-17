import sympy.Basic


@[path]
private lemma main
  {A B : Set α}
-- given
  (h₀ : A ∪ B = ∅) :
-- imply
  A = ∅ :=
-- proof
  (show A = ∅ ∧ B = ∅ by simpa using h₀).1


-- created on 2026-10-11
-- updated on 2026-10-17
