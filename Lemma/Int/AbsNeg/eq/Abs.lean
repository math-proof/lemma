import sympy.Basic


@[main]
private lemma main
  [Lattice α]
  [AddGroup α]
  {a : α} :
-- imply
  |-a| = |a| :=
-- proof
  abs_neg a


-- created on 2025-04-18
