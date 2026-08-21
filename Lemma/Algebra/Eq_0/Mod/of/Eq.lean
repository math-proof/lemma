import sympy.Basic


@[main]
private lemma main
  {a b d : ℤ}
-- given
  (h : a = b) :
-- imply
  (a - b) % d = 0 := by
-- proof
  rw [h, sub_self, Int.zero_emod]


-- created on 2018-11-23
-- updated on 2026-08-20
