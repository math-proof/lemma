module
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Def.Analysis.InnerProductSpace.DiscreteSpectrum.Part3
open scoped BigOperators


public section

/-
Author: Muse Spark 1.3
-/
namespace NonnegativeDiscreteSpectrum

/-- The `σ = 0` endpoint recovers the counting function, since every
summand has strictly positive base. -/
@[simp] theorem rieszMean_zero
    (S : NonnegativeDiscreteSpectrum) (Λ : ℝ) :
    S.rieszMean 0 Λ = S.countingFunction Λ := by
  simp [rieszMean, countingFunction]

end NonnegativeDiscreteSpectrum
