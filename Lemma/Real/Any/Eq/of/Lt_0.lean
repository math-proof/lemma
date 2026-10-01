import sympy.Basic


@[main]
private lemma main
  {x : ℝ}
-- given
  (h : x < 0) :
-- imply
  ∃ v > 0, x = -v :=
-- proof
  ⟨-x, by linarith, by ring⟩


-- created on 2026-09-27
