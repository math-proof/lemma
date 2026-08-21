import sympy.core.power
import sympy.Basic


@[main]
private lemma main
  [CommSemiring α]
  {x y : α} :
-- imply
  (x + y) ^ 4 =
    x⁴ + 4 * x³ * y + 6 * x² * y² + 4 * x * y³ + y⁴ := by
-- proof
  ring


-- created on 2018-08-17
-- updated on 2026-08-20
