import sympy.Basic


@[main]
private lemma main
  [Lattice α]
  [AddCommGroup α]
  [AddLeftMono α]
-- given
  (a b : α) :
-- imply
  |a + b| ≤ |a| + |b| :=
-- proof
  abs_add_le a b


-- created on 2025-12-08
