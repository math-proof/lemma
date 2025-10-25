import sympy.polys.polyroots
import sympy.Basic


@[main]
private lemma main
  {x : ℂ} :
-- imply
  x = (∜x)⁴ := by
-- proof
  simp [Root.quartic]


-- created on 2024-07-01
