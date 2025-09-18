import Lemma.Basic


@[main]
private lemma main
  {e : α}
  {A B : Set α}
-- given
  (h : e ∉ A ∨ e ∉ B) :
-- imply
  e ∉ A ∩ B := by
-- proof
  contrapose! h
  assumption


-- created on 2025-07-19
