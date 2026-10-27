import Initialize.Tactic.Attr.Basic
import Theorem.Algebra.Power.Part2


@[path]
private lemma main
  [CommSemiring α]
-- given
  (a b c : α) :
-- imply
  (a + b + c)² = a² + b² + c² + 2 * (a * b + b * c + c * a) := by
-- proof
  ring


-- created on 2018-06-06
-- updated on 2026-10-26
