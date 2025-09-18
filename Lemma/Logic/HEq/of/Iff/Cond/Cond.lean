import Lemma.Basic


@[main]
private lemma main
  {p q: Prop}
-- given
  (h_p : p)
  (h_q : q)
  (h : p ↔ q):
-- imply
  HEq h_p h_q := by
-- proof
  aesop


-- created on 2025-07-13
