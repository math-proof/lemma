import Instance.Algebra.Polynomial.Polyroots
import Notation.Algebra.Polynomial.Polyroots
import Notation.Algebra.Power
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x : ℂ} :
-- imply
  (√x)² = x := by
-- proof
  simp [Root.sqrt]


-- created on 2024-07-01
-- updated on 2026-11-22
