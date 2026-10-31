import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Algebra.BigOperators.Fin
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Real

/-- Probability density of the chi-square distribution with `n` degrees of freedom
(textbook / sympy):
`pdf(x) = 1 / (2^(n/2) * Gamma(n/2)) * x^(n/2 - 1) * exp(-x/2)` for `x ≥ 0`, else `0`.
Equals Mathlib `gammaPDFReal` at shape `n/2` and rate `1/2`. -/
noncomputable def chiSquarePDF (n : ℕ) (x : ℝ) : ℝ :=
  gammaPDFReal ((n : ℝ) / 2) (1 / 2) x


/-- The chi-square distribution with `n` degrees of freedom on `ℝ`
(textbook density definition).
For `n = 0` this is `Measure.dirac 0` (empty sum of squares); for `n > 0` it is
`gammaMeasure (n/2) (1/2)`. -/
noncomputable def chiSquare (n : ℕ) : Measure ℝ :=
  if n = 0 then Measure.dirac 0 else gammaMeasure ((n : ℝ) / 2) (1 / 2)

end Real


/-- Pushforward of `n` i.i.d. standard normals under sum of squares.
This is a characterization of chi-square used in proofs (e.g. Random's
`Distributed.ChiSquared.of.All_Distributed_Gaussian.All_Indep`), not the
definition of `Real.chiSquare`. -/
noncomputable def sumSqGaussians (n : ℕ) : Measure ℝ :=
  (Measure.pi fun _ : Fin n ↦ gaussianReal 0 1).map
    (fun x : Fin n → ℝ ↦ ∑ i, (x i) ^ 2)


instance instIsProbabilityMeasureChiSquare (n : ℕ) :
    IsProbabilityMeasure (Real.chiSquare n) := by
  by_cases h : n = 0
  · subst h
    simpa [Real.chiSquare] using
      (inferInstance : IsProbabilityMeasure (Measure.dirac (0 : ℝ)))
  · have hn : 0 < (n : ℝ) / 2 := by
      have : (0 : ℕ) < n := Nat.pos_of_ne_zero h
      positivity
    have hr : 0 < (1 / 2 : ℝ) := by positivity
    simpa [Real.chiSquare, h] using isProbabilityMeasure_gammaMeasure hn hr


instance instIsProbabilityMeasureSumSqGaussians (n : ℕ) :
    IsProbabilityMeasure (sumSqGaussians n) :=
  inferInstanceAs (IsProbabilityMeasure
    ((Measure.pi fun _ : Fin n ↦ gaussianReal 0 1).map
      (fun x : Fin n → ℝ ↦ ∑ i, (x i) ^ 2)))
