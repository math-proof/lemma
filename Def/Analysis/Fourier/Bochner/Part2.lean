/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

module

public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.MeasureTheory.Measure.LevyConvergence
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Algebra.Order.Round
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Separation.CompletelyRegular
public import Theorem.Analysis.Fourier.Bochner.Part2

@[expose] public section

section

open MeasureTheory Complex

open scoped BigOperators

namespace Fourier.BochnerWanted

/-- Step sizes `h_n = 1/(n+1)` for the Fejér approximation sequence. -/
noncomputable def bochnerH (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

/-- Degrees `N_n = (n+1)^2` for the Fejér approximation sequence. -/
noncomputable def bochnerN (n : ℕ) : ℕ := (n + 1) ^ 2

/-- Rounded lattice index `m_n(t) = round(t / h_n)`. -/
noncomputable def bochnerM (t : ℝ) (n : ℕ) : ℤ := round (t / bochnerH n)

/-- Approximation sequence `ν_n = bochnerApprox f h_n N_n`. -/
noncomputable def bochnerSeq (f : ℝ → ℂ) (n : ℕ) : Measure ℝ :=
  bochnerApprox f (bochnerH n) (bochnerN n)

end Fourier.BochnerWanted
end
