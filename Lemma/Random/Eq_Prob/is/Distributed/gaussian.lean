import Mathlib.Probability.Distributions.Gaussian.Real
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory


/--
A random variable whose law is the density `gaussianPDF` is Gaussian.
-/
@[path]
private lemma main
  [MeasurableSpace Ω]
  {π : Measure Ω}
  {x : Ω → ℝ}
  {μ : ℝ}
  {v : NNReal}
-- given
  (h₀ : v ≠ 0)
  (h₁ : π.map x = volume.withDensity (gaussianPDF μ v)) :
-- imply
  π.map x = gaussianReal μ v := by
-- proof
  rw [h₁, gaussianReal_of_var_ne_zero _ h₀]


-- created on 2023-04-10
-- updated on 2026-10-26
