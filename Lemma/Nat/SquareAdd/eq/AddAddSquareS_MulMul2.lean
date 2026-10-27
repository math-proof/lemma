import Theorem.Algebra.Power.Part2
import Initialize.Tactic.Attr.Basic


@[path, comm]
private lemma main
  [CommSemiring α]
  {a b : α} :
-- imply
  (a + b)² = a² + b² + 2 * a * b :=
-- proof
  add_sq' a b


-- created on 2024-07-01
