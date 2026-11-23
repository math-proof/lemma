/-
Author: Muse Spark 1.3
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Def.Analysis.InnerProductSpace.DiscreteSpectrum

@[expose] public section

open scoped BigOperators


namespace NonnegativeDiscreteSpectrum

/-- The strict sublevel set is finite: monotonicity plus divergence to `+∞`
bounds it by an initial segment. -/
theorem sublevelSet_finite
    (S : NonnegativeDiscreteSpectrum) (Λ : ℝ) :
    (S.sublevelSet Λ).Finite := by
  obtain ⟨N, hN⟩ := Filter.tendsto_atTop_atTop.mp S.tendsto_eigenvalue_atTop Λ
  refine Set.Finite.subset (Finset.finite_toSet (Finset.range N)) fun j hj => ?_
  simp only [sublevelSet, Set.mem_ofPred_eq] at hj
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra h
  have hle : N ≤ j := not_lt.mp h
  exact (not_le.mpr hj) (hN j hle)

end NonnegativeDiscreteSpectrum
