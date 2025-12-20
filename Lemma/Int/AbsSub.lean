import sympy.Basic


@[main]
private lemma Comm
  [Lattice α]
  [AddGroup α]
-- given
  (a b : α) :
-- imply
  |a - b| = |b - a| :=
-- proof
  abs_sub_comm a b


-- created on 2025-12-08
