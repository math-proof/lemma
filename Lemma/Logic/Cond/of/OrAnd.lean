import Lemma.Basic


@[main]
private lemma main
  {p q : Prop}
-- given
  (h : p ∧ q ∨ p) :
-- imply
  p := by
-- proof
  obtain h_pq | hp := h
  ·
    exact h_pq.left
  ·
    assumption


-- created on 2025-04-14
