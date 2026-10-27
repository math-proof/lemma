/-
Authors: Adam Kiezun, Muse Spark 1.3
-/
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Ring
import Mathlib.Topology.Separation.CompletelyRegular
import Theorem.Analysis.Fourier.Bochner


section

open MeasureTheory Complex

open scoped BigOperators

namespace Fourier.BochnerWanted

noncomputable def bochnerKernel (f : ℝ → ℂ) (h : ℝ) (N : ℕ) (ξ : ℝ) : ℂ :=
  ∑ j : Fin N, ∑ l : Fin N,
    f (((j : ℝ) - (l : ℝ)) * h) * cexp (((-(((j : ℝ) - (l : ℝ)) * h * ξ) : ℝ) : ℂ) * I)

/-- Lattice nodes `ξ_r = π (r - N) / (N h)` for the discrete Fejér approximation. -/
noncomputable def bochnerNode (h : ℝ) (N : ℕ) (r : ℕ) : ℝ :=
  Real.pi * ((r : ℝ) - (N : ℝ)) / ((N : ℝ) * h)

/-- Fejér weights `w_r = Re K(ξ_r) / (2N²)`. -/
noncomputable def bochnerWeight (f : ℝ → ℂ) (h : ℝ) (N : ℕ) (r : ℕ) : ℝ :=
  (bochnerKernel f h N (bochnerNode h N r)).re / (2 * (N : ℝ) ^ 2)

/-- Discrete Fejér/Herglotz approximation measure `ν = Σ_r ofReal(w_r) • dirac(ξ_r)`. -/
noncomputable def bochnerApprox (f : ℝ → ℂ) (h : ℝ) (N : ℕ) : Measure ℝ :=
  ∑ r ∈ Finset.range (2 * N),
    ENNReal.ofReal (bochnerWeight f h N r) • Measure.dirac (bochnerNode h N r)

end Fourier.BochnerWanted
end
