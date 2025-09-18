import Lemma.Basic


@[main]
private lemma main
  {a : α}
  {b : β}
-- given
  (h : α = β) :
-- imply
  HEq a b ↔ a = cast h.symm b := by
-- proof
  aesop


-- created on 2025-07-16
