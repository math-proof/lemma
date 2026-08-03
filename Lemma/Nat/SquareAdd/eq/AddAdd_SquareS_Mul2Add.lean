import sympy.Basic
import sympy.core.power


@[main]
private lemma main
  [CommSemiring α]
-- given
  (a b c : α) :
-- imply
  (a + b + c)² = a² + b² + c² + 2 * (a * b + b * c + c * a) := by
-- proof
  ring


-- created on 2018-06-06
-- updated on 2026-08-03
