/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/QuotientFDerivStep.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Analysis.Complex.Basic
public import Def.v1.Atlas.DifferentialAnalysis.code.SmoothingOperators
public import Theorem.Real.Atlas.v1.DifferentialAnalysis.code.SmoothingOperators
@[expose] public section

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
