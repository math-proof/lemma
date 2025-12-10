import sympy.Basic


@[main]
private lemma main
  [Lattice α] [AddGroup α] [AddLeftMono α] [AddRightMono α]
-- given
  (a : α) :
-- imply
  |a| ≥ 0 :=
-- proof
  abs_nonneg a


-- created on 2025-01-14
