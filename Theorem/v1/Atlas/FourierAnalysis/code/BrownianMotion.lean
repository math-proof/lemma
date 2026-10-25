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
import Def.v1.Atlas.FourierAnalysis.code.BrownianMotion.Part3
open MeasureTheory ProbabilityTheory Complex Matrix
open scoped ENNReal NNReal


namespace GaussianLinearTransform

/-- A real-valued Gaussian random variable with law $\mathcal{N}(0, v)$ lies in $L^2(P)$. -/
lemma memLp_two_of_hasLaw {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {v : ℝ≥0} (hlaw : HasLaw X (gaussianReal 0 v) P) :
    MemLp X 2 P :=
  hlaw.hasGaussianLaw.memLp_two

/-- The partial sum $S_n = \sum_{k < n} X_k$ of Gaussian random variables lies in $L^2(P)$. -/
lemma memLp_partialSum {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℕ → Ω → ℝ} {v : ℕ → ℝ≥0}
    (hgauss : ∀ k, HasLaw (X k) (gaussianReal 0 (v k)) P) (n : ℕ) :
    MemLp (fun ω => ∑ k ∈ range n, X k ω) 2 P :=
  memLp_finset_sum _ (fun k _ => memLp_two_of_hasLaw (hgauss k))


end GaussianLinearTransform
