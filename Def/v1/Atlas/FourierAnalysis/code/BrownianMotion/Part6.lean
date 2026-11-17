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
public import Structure.v1.Atlas.FourierAnalysis.code.BrownianMotion.Part4

@[expose] public section

open MeasureTheory ProbabilityTheory Complex Matrix
open scoped ENNReal NNReal


namespace GaussianLinearTransform

noncomputable def wienerCoeff (n : ℕ) (t : Fin n → ℝ) (c : Fin n → ℝ) (k : ℕ) : ℝ :=
  if k = 0 then wienerC0 * ∑ j : Fin n, c j * t j
  else wienerC1 * ∑ j : Fin n, c j * Real.sin (↑k * t j) / ↑k

noncomputable def wienerCoeffVar (n : ℕ) (t : Fin n → ℝ) (c : Fin n → ℝ) : ℕ → NNReal :=
  fun k => ⟨(wienerCoeff n t c k) ^ 2, sq_nonneg _⟩

noncomputable def wienerBasisCoeff (s : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then wienerC0 * s
  else wienerC1 * Real.sin (↑k * s) / ↑k

end GaussianLinearTransform
