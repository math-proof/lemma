/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/FourierAnalysis/code/BrownianMotion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Distributions.Gaussian.Basic
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.CentralLimitTheorem
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.PSeries
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Conformal
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Real.Pi.Bounds
public import Structure.v1.Atlas.FourierAnalysis.code.BrownianMotion.Part2

@[expose] public section

open MeasureTheory ProbabilityTheory Complex Matrix
open scoped ENNReal NNReal


namespace GaussianLinearTransform

noncomputable def randomPowerSeries {Ω : Type*} [MeasurableSpace Ω]
    (a : ℕ → Ω → ℝ) (z : ℂ) (ω : Ω) : ℂ :=
  ∑' k : ℕ, (a (k + 1) ω : ℂ) * z ^ (k + 1) / (↑(k + 1 : ℕ) : ℂ)

noncomputable def powerSeriesDeriv {Ω : Type*} [MeasurableSpace Ω]
    (a : ℕ → Ω → ℝ) (z : ℂ) (ω : Ω) : ℂ :=
  ∑' j : ℕ, (a (j + 1) ω : ℂ) * z ^ j

noncomputable def weightedGradientIntegral {Ω : Type*} [MeasurableSpace Ω]
    (a : ℕ → Ω → ℝ) (β : ℝ) (ω : Ω) : ℝ :=
  ∫ t in (0 : ℝ)..(2 * Real.pi),
    ∫ r in (0 : ℝ)..1,
      (4 * ‖powerSeriesDeriv a (↑r * Complex.exp (↑t * Complex.I)) ω‖ ^ 4) *
      (1 - r) ^ β * r

noncomputable def weightedGradientIntegralENNReal {Ω : Type*} [MeasurableSpace Ω]
    (a : ℕ → Ω → ℝ) (β : ℝ) (ω : Ω) : ENNReal :=
  ∫⁻ t : ℝ in Set.Icc 0 (2 * Real.pi),
    ∫⁻ r : ℝ in Set.Icc 0 1,
      ENNReal.ofReal
        ((4 * ‖powerSeriesDeriv a (↑r * Complex.exp (↑t * Complex.I)) ω‖ ^ 4) *
         (1 - r) ^ β * r)

end GaussianLinearTransform
