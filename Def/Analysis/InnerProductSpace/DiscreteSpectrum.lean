/-
Author: Muse Spark 1.3
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Set.Card
import Mathlib.Order.Filter.AtTopBot.Basic
import Theorem.Analysis.InnerProductSpace.DiscreteSpectrum
open scoped BigOperators


namespace NonnegativeDiscreteSpectrum

/-- Strict sublevel set: indices with eigenvalue strictly below the cutoff.
The strict inequality encodes the standard convention `(Λ - E_j)_+^0 = 1`
only when `E_j < Λ`, avoiding `0 ^ 0 = 1` at the cutoff. -/
def sublevelSet (S : NonnegativeDiscreteSpectrum) (Λ : ℝ) : Set ℕ :=
  {j | S j < Λ}

end NonnegativeDiscreteSpectrum
