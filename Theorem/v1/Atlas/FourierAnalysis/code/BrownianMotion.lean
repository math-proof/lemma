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
public import Def.v1.Atlas.FourierAnalysis.code.BrownianMotion.Part3
open MeasureTheory ProbabilityTheory Complex Matrix
open scoped ENNReal NNReal

public section

namespace GaussianLinearTransform

/-- A real-valued Gaussian random variable with law $\mathcal{N}(0, v)$ lies in $L^2(P)$. -/
lemma memLp_two_of_hasLaw {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {v : NNReal} (hlaw : HasLaw X (gaussianReal 0 v) P) :
    MemLp X 2 P :=
  hlaw.hasGaussianLaw.memLp_two

/-- The partial sum $S_n = \sum_{k < n} X_k$ of Gaussian random variables lies in $L^2(P)$. -/
lemma memLp_partialSum {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℕ → Ω → ℝ} {v : ℕ → NNReal}
    (hgauss : ∀ k, HasLaw (X k) (gaussianReal 0 (v k)) P) (n : ℕ) :
    MemLp (fun ω => ∑ k ∈ range n, X k ω) 2 P :=
  memLp_finset_sum _ (fun k _ => memLp_two_of_hasLaw (hgauss k))


end GaussianLinearTransform
