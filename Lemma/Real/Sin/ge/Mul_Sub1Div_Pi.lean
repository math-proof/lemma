import Lemma.Real.GeSin.of.Ge_0.quadratic
import Lemma.Real.GeSin.of.Le_0.quadratic
open Real


@[path]
private lemma main
  {x : ℝ} :
-- imply
  Real.sin x ≥ x * (1 - x / Real.pi) := by
-- proof
  if h₀ : 0 ≤ x then
    apply GeSin.of.Ge_0.quadratic h₀
  else
    apply GeSin.of.Le_0.quadratic
    linarith


-- created on 2023-10-03
-- updated on 2026-10-17
