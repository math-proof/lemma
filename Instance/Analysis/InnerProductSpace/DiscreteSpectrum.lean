/-
Author: Muse Spark 1.3
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Structure.Analysis.InnerProductSpace.DiscreteSpectrum

@[expose] public section

open scoped BigOperators


namespace NonnegativeDiscreteSpectrum

instance : CoeFun NonnegativeDiscreteSpectrum (fun _ => ℕ → ℝ) :=
  ⟨NonnegativeDiscreteSpectrum.eigenvalue⟩

end NonnegativeDiscreteSpectrum
