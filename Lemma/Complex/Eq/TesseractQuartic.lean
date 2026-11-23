import Instance.Algebra.Polynomial.Polyroots
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x : ℂ} :
-- imply
  x = (Root.quartic x) ^ 4 := by
-- proof
  simp [Root.quartic]


-- created on 2024-07-01
-- updated on 2026-11-22
