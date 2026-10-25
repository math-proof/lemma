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
import Instance.v1.Atlas.DifferentialAnalysis.code.QuotientFDerivStep
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
