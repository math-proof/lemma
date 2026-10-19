import Mathlib.Probability.Independence.Integration
import Lemma.Random.Var.eq.Integral
import Lemma.Random.Cov.eq.Integral
open MeasureTheory


@[path]
private lemma main
  [MeasurableSpace Ω]
  {π : Measure Ω}
  {x : Ω → ℝ}
-- given
  [PSpace π x] :
-- imply
  ℂ𝕠𝕧 π x x = 𝕍𝕒𝕣 π x := by
-- proof
  rw [Random.Var.eq.Integral, Random.Cov.eq.Integral]
  simp only [sq]


-- created on 2023-04-19
