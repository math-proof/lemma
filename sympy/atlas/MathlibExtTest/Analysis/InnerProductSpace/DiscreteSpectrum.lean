/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/InnerProductSpace/DiscreteSpectrum.lean -/

/-
Author: Muse Spark 1.3
-/

import sympy.atlas.Analysis.InnerProductSpace.DiscreteSpectrum
import Lemma.Matrix.FiniteSublevelSet
import Lemma.Matrix.Eq.of.All_Eq
import Lemma.Matrix.In_SublevelFinset.is.Lt
import Lemma.Matrix.RieszMean0.eq.CountingFunction

/-!
# Tests for the generic nonnegative discrete-spectrum counting layer
-/

open scoped BigOperators

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

-- Every public projection and theorem is exercised below.

example : dupSpectrum.eigenvalue = dupEigen := rfl

example (j : ℕ) : 0 ≤ dupSpectrum.eigenvalue j :=
  dupSpectrum.nonnegative_eigenvalue j

example : Monotone dupSpectrum.eigenvalue := dupSpectrum.monotone_eigenvalue

example : Filter.Tendsto dupSpectrum.eigenvalue Filter.atTop Filter.atTop :=
  dupSpectrum.tendsto_eigenvalue_atTop

example : dupSpectrum.sublevelSet 1 = {j | dupSpectrum j < 1} := rfl

example : (dupSpectrum.sublevelSet 1).Finite := dupSpectrum.sublevelSet_finite 1

example (j : ℕ) : j ∈ dupSpectrum.sublevelFinset 1 ↔ dupSpectrum j < 1 :=
  dupSpectrum.mem_sublevelFinset 1 j

-- A repeated eigenvalue is counted once per index (multiplicity).
example : dupEigen 0 = dupEigen 1 := rfl

example : (0 : ℕ) ∈ dupSpectrum.sublevelFinset 1 := by
  rw [NonnegativeDiscreteSpectrum.mem_sublevelFinset]
  change dupEigen 0 < 1
  norm_num [dupEigen]

example : (1 : ℕ) ∈ dupSpectrum.sublevelFinset 1 := by
  rw [NonnegativeDiscreteSpectrum.mem_sublevelFinset]
  change dupEigen 1 < 1
  norm_num [dupEigen]

-- An eigenvalue equal to the cutoff is excluded from the strict sublevel.
example : dupEigen 2 = 1 := by norm_num [dupEigen]

example : (2 : ℕ) ∉ dupSpectrum.sublevelFinset 1 := by
  rw [NonnegativeDiscreteSpectrum.mem_sublevelFinset]
  change ¬ dupEigen 2 < 1
  norm_num [dupEigen]

-- The `σ = 0` Riesz mean recovers the counting function.
example : dupSpectrum.rieszMean 0 1 = dupSpectrum.countingFunction 1 :=
  dupSpectrum.rieszMean_zero 1

example : dupSpectrum.rieszMean 0 1 = 2 := by
  rw [dupSpectrum.rieszMean_zero, dup_counting_one]
  norm_num

-- A Riesz mean with `σ = 1` over the two surviving terms.
example : dupSpectrum.rieszMean 1 1 = 2 := by
  change ∑ j ∈ dupSpectrum.sublevelFinset 1, Real.rpow (1 - dupSpectrum j) 1 = 2
  rw [dup_sublevelFinset_one]
  have e0 : dupSpectrum (0 : ℕ) = 0 := by
    change dupEigen 0 = 0
    norm_num [dupEigen]
  have e1 : dupSpectrum (1 : ℕ) = 0 := by
    change dupEigen 1 = 0
    norm_num [dupEigen]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton,
    e0, e1]
  have hr : ∀ x : ℝ, x.rpow (1 : ℝ) = x := fun x => Real.rpow_one x
  rw [hr]
  norm_num

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

-- Pointwise extensionality identifies spectra with the same eigenvalue function.
example : dupSpectrum = dupSpectrumAlt := by
  ext j
  rfl

end NonnegativeDiscreteSpectrumTest
