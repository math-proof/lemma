import Lemma.Real.GeSin.of.Ge_0.quadratic
open Real


@[path]
private lemma main
  {x : ℝ}
  (h₀ : x ∈ Set.Icc 0 (Real.pi / 2)) :
-- imply
  Real.sin x ≥ x * (1 - x / Real.pi) := by
-- proof
  apply GeSin.of.Ge_0.quadratic h₀.1


-- created on 2026-10-11
-- updated on 2026-10-17
