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
import Def.v1.Atlas.FourierAnalysis.code.BrownianMotion
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
