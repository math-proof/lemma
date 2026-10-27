import Theorem.Algebra.Power.Part2
import Initialize.Tactic.Attr.Basic


@[path]
private lemma Comm
  [CommRing α]
-- given
  (a b : α) :
-- imply
  (a - b)² = (b - a)² := by
-- proof
  ring


-- created on 2025-12-20
