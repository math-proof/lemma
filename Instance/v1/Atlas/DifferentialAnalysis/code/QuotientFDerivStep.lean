/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/QuotientFDerivStep.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.Complex.Basic
import Def.v1.Atlas.DifferentialAnalysis.code.SmoothingOperators
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.SmoothingOperators
open MvPolynomial Complex


noncomputable section

/-- The scalar multiplication of `ℝ` on `ℂ` is continuous, exhibited as a
`ContinuousSMul` instance.  This is used downstream when differentiating
real-linear maps with complex codomain. -/
instance instContinuousSMulRealComplex : ContinuousSMul ℝ ℂ where
  continuous_smul := by
    simp only [Complex.real_smul]
    exact (Complex.continuous_ofReal.comp continuous_fst).mul continuous_snd

end
