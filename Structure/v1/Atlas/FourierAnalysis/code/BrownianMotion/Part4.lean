/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/FourierAnalysis/code/BrownianMotion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Distributions.Gaussian.Basic
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.NumberTheory.ZetaValues
import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Conformal
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Real.Pi.Bounds
import Def.v1.Atlas.FourierAnalysis.code.BrownianMotion.Part5
open MeasureTheory ProbabilityTheory Complex Matrix
open scoped ENNReal NNReal


namespace GaussianLinearTransform

structure IsWienerBrownianMotion {Ω : Type*} [MeasurableSpace Ω]
    (W : ℝ → Ω → ℝ) (P : Measure Ω) : Prop where
  zero_at_origin : ∀ ω, W 0 ω = 0
  mean_zero : ∀ t, 0 ≤ t → t ≤ Real.pi → ∫ ω, W t ω ∂P = 0
  gaussian_linear_comb : ∀ (n : ℕ) (t : Fin n → ℝ),
    (∀ j, 0 ≤ t j ∧ t j ≤ Real.pi) → ∀ (c : Fin n → ℝ),
    HasGaussianLaw (fun ω => ∑ j, c j * W (t j) ω) P
  covariance_eq_min : ∀ s t, 0 ≤ s → s ≤ Real.pi → 0 ≤ t → t ≤ Real.pi →
    ∫ ω, W s ω * W t ω ∂P = min s t
  ae_continuousOn : ∀ᵐ ω ∂P, ContinuousOn (fun t => W t ω) (Icc 0 Real.pi)

end GaussianLinearTransform
