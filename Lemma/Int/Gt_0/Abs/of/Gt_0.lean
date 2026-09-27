import sympy.Basic


@[main]
private lemma main
  [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
  {x : α}
-- given
  (h₀ : x > 0) :
-- imply
  |x| > 0 :=
-- proof
  abs_pos.mpr h₀.ne'


-- created on 2026-09-26
