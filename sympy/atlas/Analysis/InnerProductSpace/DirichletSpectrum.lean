/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/InnerProductSpace/DirichletSpectrum.lean -/

/-
Author: Muse Spark 1.3
-/

import sympy.atlas.Analysis.InnerProductSpace.DiscreteSpectrum
import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.LinearAlgebra.Dimension.Finrank

open TopologicalSpace MeasureTheory

namespace DirichletLaplacian

/-- Smooth compactly supported test functions on `Ω`: the Dirichlet form core.
Support inside `Ω` comes from the bundled `TestFunction` type, not from an
unchecked function predicate. -/
abbrev SmoothTestSpace {n : ℕ} (Ω : Opens (EuclideanSpace ℝ (Fin n))) :=
  TestFunction Ω ℝ ⊤

/-- Rayleigh quotient of a smooth compactly supported test function: the
full-space `volume` integral of the squared operator norm of `fderiv` divided
by the full-space `volume` integral of `|f| ^ 2`. -/
noncomputable def rayleighQuotient {n : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin n))}
    (f : SmoothTestSpace Ω) : ℝ :=
  (∫ x, ‖fderiv ℝ (f : EuclideanSpace ℝ (Fin n) → ℝ) x‖ ^ 2 ∂volume) /
    (∫ x, |f x| ^ 2 ∂volume)

/-- Zero-based Courant--Fischer min--max value at index `j`: the infimum, over
`(j + 1)`-dimensional submodules `V` of the smooth test space, of the supremum
of the Rayleigh quotient over the nonzero vectors of `V`. This is a
definition only; no existence, nonnegativity, monotonicity, divergence, or
operator-spectrum claim is made here. -/
noncomputable def variationalEigenvalue {n : ℕ}
    (Ω : Opens (EuclideanSpace ℝ (Fin n))) (j : ℕ) : ℝ :=
  sInf {a : ℝ | ∃ V : Submodule ℝ (SmoothTestSpace Ω),
    Module.finrank ℝ ↥V = j + 1 ∧
      a = sSup {q : ℝ | ∃ f : ↥V,
        (f : SmoothTestSpace Ω) ≠ 0 ∧
          rayleighQuotient (f : SmoothTestSpace Ω) = q}}

end DirichletLaplacian

/-- A nonnegative discrete spectrum is the Dirichlet spectrum of `Ω` when every
zero-based sequence value equals the variational min--max value. This is a
pointwise equality, not an unconstrained certificate field. -/
def NonnegativeDiscreteSpectrum.IsDirichletSpectrum {n : ℕ}
    (S : NonnegativeDiscreteSpectrum)
    (Ω : Opens (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ j, S j = DirichletLaplacian.variationalEigenvalue Ω j

namespace EuclideanLaplacian

/-- Real volume of the Euclidean unit ball in `ℝⁿ`: the canonical `volume`
measure of `Metric.ball 0 1`, coerced to `ℝ` via `Measure.real`. -/
noncomputable def unitBallVolume (n : ℕ) : ℝ :=
  (volume : Measure (EuclideanSpace ℝ (Fin n))).real
    (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)

/-- Real volume of an open domain `Ω ⊂ ℝⁿ`: the canonical `volume` measure of
the underlying set, coerced to `ℝ` via `Measure.real`. -/
noncomputable def domainVolume {n : ℕ}
    (Ω : Opens (EuclideanSpace ℝ (Fin n))) : ℝ :=
  (volume : Measure (EuclideanSpace ℝ (Fin n))).real (Ω : Set _)

/-- Semiclassical counting coefficient `ωₙ |Ω| / (2π)ⁿ`: the product of the
unit-ball volume and the domain volume, divided by `(2π)ⁿ`. -/
noncomputable def semiclassicalCountingCoefficient {n : ℕ}
    (Ω : Opens (EuclideanSpace ℝ (Fin n))) : ℝ :=
  unitBallVolume n * domainVolume Ω / (2 * Real.pi) ^ n

/-- Zero-based eigenvalue benchmark at index `j`: `(2π)²` times the real power
of the one-based eigenvalue number `((j + 1 : ℕ) : ℝ)` divided by
`ωₙ |Ω|`, with exponent `2 / (n : ℝ)`. The one-based numerator is kept explicit
because `NonnegativeDiscreteSpectrum` is zero-based. -/
noncomputable def polyaEigenvalueBenchmark {n : ℕ}
    (Ω : Opens (EuclideanSpace ℝ (Fin n))) (j : ℕ) : ℝ :=
  (2 * Real.pi) ^ 2 *
    ((((j + 1 : ℕ) : ℝ) /
      (unitBallVolume n * domainVolume Ω)) ^ (2 / (n : ℝ)))

theorem unitBallVolume_nonneg (n : ℕ) : 0 ≤ unitBallVolume n :=
  measureReal_nonneg

theorem domainVolume_nonneg {n : ℕ}
    (Ω : Opens (EuclideanSpace ℝ (Fin n))) : 0 ≤ domainVolume Ω :=
  measureReal_nonneg

theorem semiclassicalCountingCoefficient_nonneg {n : ℕ}
    (Ω : Opens (EuclideanSpace ℝ (Fin n))) :
    0 ≤ semiclassicalCountingCoefficient Ω := by
  unfold semiclassicalCountingCoefficient
  exact div_nonneg
    (mul_nonneg (unitBallVolume_nonneg n) (domainVolume_nonneg Ω))
    (pow_nonneg (mul_nonneg (by norm_num) Real.pi_nonneg) n)

theorem polyaEigenvalueBenchmark_nonneg {n : ℕ}
    (Ω : Opens (EuclideanSpace ℝ (Fin n))) (j : ℕ) :
    0 ≤ polyaEigenvalueBenchmark Ω j := by
  unfold polyaEigenvalueBenchmark
  exact mul_nonneg
    (pow_nonneg (mul_nonneg (by norm_num) Real.pi_nonneg) 2)
    (Real.rpow_nonneg
      (div_nonneg (Nat.cast_nonneg _)
        (mul_nonneg (unitBallVolume_nonneg n) (domainVolume_nonneg Ω))) _)

end EuclideanLaplacian
