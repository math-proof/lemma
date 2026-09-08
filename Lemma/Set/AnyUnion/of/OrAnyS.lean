import sympy.Basic


@[main]
private lemma main
  {A B : Set α}
  {f : α → Prop}
-- given
  (h : (∃ x ∈ A, f x) ∨ ∃ x ∈ B, f x) :
-- imply
  ∃ x ∈ A ∪ B, f x := by
-- proof
  aesop


-- created on 2026-09-08
