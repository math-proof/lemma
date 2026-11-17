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
public import Def.v1.Atlas.FourierAnalysis.code.BrownianMotion
public section

open MeasureTheory ProbabilityTheory Complex Matrix
open scoped ENNReal NNReal


namespace GaussianLinearTransform

structure HasIndependentGaussianIncrements
    {Ω : Type*} [MeasurableSpace Ω]
    (B : NNReal → Ω → ℝ) (P : Measure Ω) : Prop where
  zero_at_origin : ∀ ω, B 0 ω = 0
  indep_increments : ∀ (n : ℕ) (t : Fin (n + 1) → NNReal),
    StrictMono t → t 0 = 0 →
    iIndepFun (m := fun (_ : Fin n) => inferInstance)
      (fun (j : Fin n) (ω : Ω) => B (t j.succ) ω - B (t j.castSucc) ω) P
  gaussian_increments : ∀ (n : ℕ) (t : Fin (n + 1) → NNReal),
    StrictMono t → t 0 = 0 →
    ∀ (j : Fin n), HasLaw
      (fun ω => B (t j.succ) ω - B (t j.castSucc) ω)
      (gaussianReal 0 (t j.succ - t j.castSucc)) P

structure HasBrownianCharacterization
    {Ω : Type*} [MeasurableSpace Ω]
    (B : NNReal → Ω → ℝ) (P : Measure Ω) : Prop where
  zero_at_origin : ∀ ω, B 0 ω = 0
  gaussian_process : IsGaussianProcess B P
  mean_zero : ∀ (t : NNReal), ∫ ω, B t ω ∂P = 0
  covariance : ∀ (s t : NNReal), ∫ ω, B s ω * B t ω ∂P = min (s : ℝ) (t : ℝ)

end GaussianLinearTransform
