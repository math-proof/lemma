/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DifferentialOperators.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Distribution.Support
import Mathlib.Analysis.Distribution.FourierMultiplier
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Theorem.v1.Atlas.DifferentialAnalysis.code.DistributionSupport
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.DistributionSupport
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.SchwartzTranslateContinuity
import Theorem.v1.Atlas.DifferentialAnalysis.code.SchwartzTranslateContinuity
import Structure.v1.Atlas.DifferentialAnalysis.code.DifferentialOperators
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
  coe_injective' u v h := by cases u; cases v; congr

end SmoothZeroAtInfty
end OperatorProperties
end DifferentialOperators
end
