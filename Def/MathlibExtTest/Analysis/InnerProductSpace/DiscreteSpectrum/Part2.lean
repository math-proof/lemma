module
public import Theorem.Analysis.InnerProductSpace.DiscreteSpectrum.Part4
public import Theorem.Matrix.FiniteSublevelSet
public import Theorem.Matrix.Eq.of.All_Eq
public import Theorem.Matrix.In_SublevelFinset.is.Lt
public import Theorem.Matrix.RieszMean0.eq.CountingFunction
public import Theorem.MathlibExtTest.Analysis.InnerProductSpace.DiscreteSpectrum
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/InnerProductSpace/DiscreteSpectrum.lean -/
/-
Author: Muse Spark 1.3
-/
/-!
# Tests for the generic nonnegative discrete-spectrum counting layer
-/
namespace NonnegativeDiscreteSpectrumTest

/-- A second copy of the doubling-index spectrum with independently supplied
proof fields. -/
noncomputable def dupSpectrumAlt : NonnegativeDiscreteSpectrum where
  eigenvalue := dupEigen
  nonnegative_eigenvalue := fun j => Nat.cast_nonneg _
  monotone_eigenvalue := by
    intro a b hab
    change ((a / 2 : ℕ) : ℝ) ≤ ((b / 2 : ℕ) : ℝ)
    exact Nat.cast_le.mpr (by omega)
  tendsto_eigenvalue_atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro b
    obtain ⟨n, hn⟩ := exists_nat_ge b
    exact ⟨2 * n + 1, fun a ha => le_trans hn (Nat.cast_le.mpr (by omega))⟩

end NonnegativeDiscreteSpectrumTest
