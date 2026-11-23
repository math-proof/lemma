import Theorem.Algebra.Power.Part2
import Notation.Algebra.Power
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  [CommRing α]
  {a b : α} :
-- imply
  a² - b² = (a + b) * (a - b) := by
-- proof
  ring


-- created on 2024-12-31
-- updated on 2026-11-23
