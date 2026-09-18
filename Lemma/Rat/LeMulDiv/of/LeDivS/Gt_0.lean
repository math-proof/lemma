import sympy.Basic


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  {a b c d : α}
-- given
  (h : a / b ≤ c / d)
  (hd : 0 < d) :
-- imply
  a / b * d ≤ c := calc
-- proof
  _ ≤ c / d * d := mul_le_mul_of_nonneg_right h hd.le
  _ = _ := by grind


-- created on 2026-09-18
