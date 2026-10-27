import Theorem.Algebra.Power.Part2
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  [CommRing α]
  {x : α} :
-- imply
  x³ - y³ = (x - y) * (x² + y² + x * y) := by
-- proof
  ring


-- created on 2025-03-24
-- updated on 2026-10-26
