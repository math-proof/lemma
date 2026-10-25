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
import Theorem.v1.Atlas.FourierAnalysis.code.BrownianMotion
open MeasureTheory ProbabilityTheory Complex Matrix
open scoped ENNReal NNReal


namespace GaussianLinearTransform

/-- The partial sum $S_n = \sum_{k < n} X_k$ viewed as an element of $L^2(P)$. -/
noncomputable def partialSumLp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℕ → Ω → ℝ} {v : ℕ → ℝ≥0}
    (hgauss : ∀ k, HasLaw (X k) (gaussianReal 0 (v k)) P) (n : ℕ) :
    Lp ℝ 2 P :=
  (memLp_partialSum hgauss n).toLp _


end GaussianLinearTransform
