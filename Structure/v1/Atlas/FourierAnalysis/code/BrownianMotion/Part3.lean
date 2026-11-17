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
public import Def.v1.Atlas.FourierAnalysis.code.BrownianMotion.Part4
public section

open MeasureTheory ProbabilityTheory Complex Matrix
open scoped ENNReal NNReal


namespace GaussianLinearTransform

set_option maxHeartbeats 800000 in

/-- Predicate characterizing a Rademacher-type random variable $R : Ω → ℝ$ on
$(Ω, P)$: $R$ is measurable, has mean zero $\mathbb{E}[R] = \int R\,\mathrm{d}P = 0$,
and unit variance $\mathbb{E}[R^2] = \int R^2\,\mathrm{d}P = 1$. The canonical
example is the symmetric $\pm 1$ Bernoulli (Rademacher) variable. -/
structure IsRademacher {Ω : Type*} [MeasurableSpace Ω] (R : Ω → ℝ) (P : Measure Ω) : Prop where
  measurable : Measurable R
  mean_zero : ∫ ω, R ω ∂P = 0
  variance_one : ∫ ω, (R ω) ^ 2 ∂P = 1

end GaussianLinearTransform
