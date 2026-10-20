import Lemma.Real.GeLog.of.Ge
open Real


@[path]
private lemma main
  {x y : ℝ}
-- given
  (h₀ : x ≥ y)
  (h₁ : y > 0) :
-- imply
  Real.log x ≥ Real.log y := by
-- proof
  apply GeLog.of.Ge h₀ h₁


-- created on 2023-04-16
