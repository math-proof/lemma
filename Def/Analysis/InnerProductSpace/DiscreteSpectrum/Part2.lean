/-
Author: Muse Spark 1.3
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Set.Card
import Mathlib.Order.Filter.AtTopBot.Basic
import Theorem.Analysis.InnerProductSpace.DiscreteSpectrum.Part2
open scoped BigOperators


namespace NonnegativeDiscreteSpectrum

/-- The strict sublevel set as a finset. -/
noncomputable def sublevelFinset
    (S : NonnegativeDiscreteSpectrum) (Λ : ℝ) : Finset ℕ :=
  (S.sublevelSet_finite Λ).toFinset

end NonnegativeDiscreteSpectrum
