/-
Author: Muse Spark 1.3
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Theorem.Analysis.InnerProductSpace.DiscreteSpectrum.Part2

@[expose] public section

open scoped BigOperators


namespace NonnegativeDiscreteSpectrum

/-- The strict sublevel set as a finset. -/
noncomputable def sublevelFinset
    (S : NonnegativeDiscreteSpectrum) (Λ : ℝ) : Finset ℕ :=
  (S.sublevelSet_finite Λ).toFinset

end NonnegativeDiscreteSpectrum
