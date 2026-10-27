/-
Author: Muse Spark 1.3
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Set.Card
import Mathlib.Order.Filter.AtTopBot.Basic
import Structure.Analysis.InnerProductSpace.DiscreteSpectrum
open scoped BigOperators


namespace NonnegativeDiscreteSpectrum

instance : CoeFun NonnegativeDiscreteSpectrum (fun _ => ℕ → ℝ) :=
  ⟨NonnegativeDiscreteSpectrum.eigenvalue⟩

end NonnegativeDiscreteSpectrum
