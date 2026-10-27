/-
Author: Muse Spark 1.3
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Set.Card
import Mathlib.Order.Filter.AtTopBot.Basic
import Def.Analysis.InnerProductSpace.DiscreteSpectrum.Part3
open scoped BigOperators


namespace NonnegativeDiscreteSpectrum

/-- The `σ = 0` endpoint recovers the counting function, since every
summand has strictly positive base. -/
@[simp] theorem rieszMean_zero
    (S : NonnegativeDiscreteSpectrum) (Λ : ℝ) :
    S.rieszMean 0 Λ = S.countingFunction Λ := by
  simp [rieszMean, countingFunction]

end NonnegativeDiscreteSpectrum
