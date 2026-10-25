/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/InnerProductSpace/DiscreteSpectrum.lean -/

/-
Author: Muse Spark 1.3
-/

import Theorem.Analysis.InnerProductSpace.DiscreteSpectrum.Part3
import Lemma.Matrix.FiniteSublevelSet
import Lemma.Matrix.Eq.of.All_Eq
import Lemma.Matrix.In_SublevelFinset.is.Lt
import Lemma.Matrix.RieszMean0.eq.CountingFunction
open scoped BigOperators

/-!
# Tests for the generic nonnegative discrete-spectrum counting layer
-/


namespace NonnegativeDiscreteSpectrumTest

/-- Doubling-index eigenvalues `0, 0, 1, 1, 2, 2, …`: the value `0` has
multiplicity two (indices `0` and `1`). -/
def dupEigen : ℕ → ℝ := fun j => ((j / 2 : ℕ) : ℝ)

/-- The doubling-index spectrum as a `NonnegativeDiscreteSpectrum`. -/
noncomputable def dupSpectrum : NonnegativeDiscreteSpectrum where
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
    exact ⟨2 * n, fun a ha => le_trans hn (Nat.cast_le.mpr (by omega))⟩

end NonnegativeDiscreteSpectrumTest
