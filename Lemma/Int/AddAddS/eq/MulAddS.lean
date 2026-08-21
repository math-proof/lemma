import sympy.Basic


@[main]
private lemma main
  [CommRing α]
-- given
  (a b x y : α) :
-- imply
  a * x + a * y + (b * x + b * y) = (a + b) * (x + y) := by
-- proof
  ring


-- created on 2018-08-02
-- updated on 2026-08-20
