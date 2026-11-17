/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DifferentialOperators.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Distribution.Support
public import Mathlib.Analysis.Distribution.FourierMultiplier
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
public import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
public import Theorem.v1.Atlas.DifferentialAnalysis.code.DistributionSupport
public import Theorem.Real.Atlas.v1.DifferentialAnalysis.code.DistributionSupport
public import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.SchwartzTranslateContinuity
public import Theorem.v1.Atlas.DifferentialAnalysis.code.SchwartzTranslateContinuity
public import Def.v1.Atlas.DifferentialAnalysis.code.DifferentialOperators
open scoped SchwartzMap
open TemperedDistribution MvPolynomial


public noncomputable section

namespace DifferentialOperators

variable (n : ℕ)

section OperatorProperties

variable {n : ℕ}

/-- A **smooth function vanishing at infinity** (with all derivatives):
a smooth complex-valued function on `ℝⁿ` whose iterated derivatives of
every order tend to zero on the cocompact filter. Used as the target class
for Liouville-type uniqueness results for the Laplacian. -/
structure SmoothZeroAtInfty (n : ℕ) where
  toFun : EuclideanSpace ℝ (Fin n) → ℂ
  smooth' : ContDiff ℝ (⊤ : ℕ∞) toFun
  iteratedFDeriv_zero_at_infty' (m : ℕ) :
    Tendsto (fun x => ‖iteratedFDeriv ℝ m toFun x‖)
      (cocompact (EuclideanSpace ℝ (Fin n))) (𝓝 0)

end OperatorProperties
end DifferentialOperators
end
