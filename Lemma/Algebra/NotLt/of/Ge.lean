import Lemma.Basic


@[main]
private lemma main
  [Preorder α]
  {a b : α}
-- given
  (h : a ≥ b) :
-- imply
  ¬a < b :=
-- proof
  not_lt_of_ge h


-- created on 2025-03-29
-- updated on 2025-03-30
