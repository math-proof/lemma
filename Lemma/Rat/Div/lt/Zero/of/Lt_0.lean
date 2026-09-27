import sympy.Basic


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  {x d : α}
-- given
  (hx : x < 0)
  (hd : 0 < d) :
-- imply
  d / x < 0 :=
-- proof
  div_neg_of_pos_of_neg hd hx


-- created on 2026-09-26
