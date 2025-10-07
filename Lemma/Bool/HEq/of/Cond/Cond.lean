import Lemma.Bool.HEq.of.Iff.Cond.Cond
open Bool


@[main]
private lemma homogeneous
  {p : Prop}
-- given
  (h_a : p)
  (h_b : p) :
-- imply
  HEq h_a h_b := by
-- proof
  simp


@[main]
private lemma main
  {p q : Prop}
-- given
  (h_p : p)
  (h_q : q) :
-- imply
  HEq h_p h_q := by
-- proof
  apply HEq.of.Iff.Cond.Cond
  constructor <;>
  ·
    intro h
    assumption


-- created on 2025-07-13
