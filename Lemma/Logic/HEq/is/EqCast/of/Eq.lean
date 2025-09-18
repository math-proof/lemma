import Lemma.Basic


@[main, comm, mp, mpr]
private lemma main
  {a : α}
  {b : β}
-- given
  (h : α = β) :
-- imply
  HEq a b ↔ cast h a = b := by
-- proof
  aesop


-- created on 2025-07-16
