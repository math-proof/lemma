import Instance.Algebra.Polynomial.Polyroots
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x : ℂ} :
-- imply
  (√x)² = x := by
-- proof
  simp [Root.sqrt]


-- created on 2024-07-01
