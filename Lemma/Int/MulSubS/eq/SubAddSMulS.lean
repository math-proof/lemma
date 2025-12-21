import sympy.Basic


@[main]
private lemma main
  [CommRing α]
-- given
  (x y a b : α) :
-- imply
  (x - a) * (y - b) = x * y + a * b - (b * x + a * y) := by
-- proof
  ring


-- created on 2025-12-21
