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
public import Instance.v1.Atlas.DifferentialAnalysis.code.QuotientFDerivStep

@[expose] public section

open MvPolynomial Complex


noncomputable section

set_option maxHeartbeats 1600000

namespace DifferentialOperators

variable {n : ℕ}

/-- The continuous real-linear map sending `ξ ∈ EuclideanSpace ℝ (Fin n)` to
its `i`-th coordinate, viewed as a complex number `(ξ i : ℂ)`. -/
noncomputable def coordCLM (i : Fin n) : EuclideanSpace ℝ (Fin n) →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (PiLp.proj 2 (fun _ : Fin n => ℝ) i)

end DifferentialOperators
end
