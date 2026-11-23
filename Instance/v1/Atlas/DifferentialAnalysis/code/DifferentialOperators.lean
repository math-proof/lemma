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
public import Theorem.Real.Atlas.v1.DifferentialAnalysis.code.SchwartzTranslateContinuity
public import Theorem.v1.Atlas.DifferentialAnalysis.code.SchwartzTranslateContinuity
public import Structure.v1.Atlas.DifferentialAnalysis.code.DifferentialOperators
@[expose] public section

open scoped SchwartzMap
open TemperedDistribution MvPolynomial


noncomputable section

namespace DifferentialOperators

variable (n : ℕ)

section OperatorProperties

variable {n : ℕ}

namespace SmoothZeroAtInfty

variable {n : ℕ}

/-- `SmoothZeroAtInfty` is coercible to a function via its underlying
`toFun` field, with the obvious injectivity. -/
instance instFunLike : FunLike (SmoothZeroAtInfty n) (EuclideanSpace ℝ (Fin n)) ℂ where
  coe u := u.toFun
  coe_injective u v h := by cases u; cases v; congr

end SmoothZeroAtInfty
end OperatorProperties
end DifferentialOperators
end
