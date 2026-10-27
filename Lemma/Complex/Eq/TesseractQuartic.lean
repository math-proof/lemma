import Instance.Algebra.Polynomial.Polyroots
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x : ℂ} :
-- imply
  x = (∜x)⁴ := by
-- proof
  simp [Root.quartic]


-- created on 2024-07-01
