import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {A B : Set α}
-- given
  (h₀ : A ∪ B = ∅) :
-- imply
  A = ∅ :=
-- proof
  (show A = ∅ ∧ B = ∅ by simpa using h₀).1


-- created on 2021-05-13
-- updated on 2026-10-26
