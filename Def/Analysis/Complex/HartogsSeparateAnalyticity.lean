/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.TietzeExtension
import Theorem.Analysis.Complex.HartogsSeparateAnalyticity
/-!
# Hartogs' theorem on separate analyticity

This file proves that a scalar-valued function on finite-dimensional complex Euclidean space is
holomorphic when it is holomorphic in each coordinate separately.
-/


namespace Complex.HartogsWanted

open Set Metric Filter ContinuousLinearMap

open MeasureTheory

open scoped Topology

/-- The iterated solid-polydisc integral over equal coordinate radii. -/
noncomputable def hartogsPolydiscIntegral : {n : ℕ} →
    ((Fin n → ℂ) → ℝ) → (Fin n → ℂ) → ℝ → ℝ
  | 0, u, c, _ => u c
  | _n + 1, u, c, R =>
      ∫ z in closedBall (c 0) R,
        hartogsPolydiscIntegral (fun y ↦ u (Fin.cons z y)) (c ∘ Fin.succ) R

end Complex.HartogsWanted
