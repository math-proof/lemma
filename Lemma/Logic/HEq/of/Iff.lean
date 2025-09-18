import Lemma.Basic


@[main]
private lemma main
  {p q : Prop}
-- given
  (h : p ↔ q) :
-- imply
  HEq p q := by
-- proof
  simpa


-- created on 2025-07-08
