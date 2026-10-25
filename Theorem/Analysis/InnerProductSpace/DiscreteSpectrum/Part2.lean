/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/InnerProductSpace/DiscreteSpectrum.lean -/

/-
Author: Muse Spark 1.3
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Set.Card
import Mathlib.Order.Filter.AtTopBot.Basic
import Def.Analysis.InnerProductSpace.DiscreteSpectrum
open scoped BigOperators


namespace NonnegativeDiscreteSpectrum

/-- Exact membership for the sublevel finset. -/
@[simp] theorem mem_sublevelFinset
    (S : NonnegativeDiscreteSpectrum) (Λ : ℝ) (j : ℕ) :
    j ∈ S.sublevelFinset Λ ↔ S j < Λ := by
  rw [sublevelFinset, Set.Finite.mem_toFinset]
  rfl

end NonnegativeDiscreteSpectrum
