module
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Def.Analysis.InnerProductSpace.DiscreteSpectrum.Part2
open scoped BigOperators


public section

/-
Author: Muse Spark 1.3
-/
namespace NonnegativeDiscreteSpectrum

/-- Exact membership for the sublevel finset. -/
@[simp] theorem mem_sublevelFinset
    (S : NonnegativeDiscreteSpectrum) (Λ : ℝ) (j : ℕ) :
    j ∈ S.sublevelFinset Λ ↔ S j < Λ := by
  rw [sublevelFinset, Set.Finite.mem_toFinset]
  rfl

end NonnegativeDiscreteSpectrum
