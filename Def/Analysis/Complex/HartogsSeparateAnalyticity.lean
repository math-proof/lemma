/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Analysis.Calculus.FDeriv.Partial
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.Topology.Baire.CompleteMetrizable
public import Mathlib.Topology.TietzeExtension
public import Theorem.Analysis.Complex.HartogsSeparateAnalyticity

@[expose] public section

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
