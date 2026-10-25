/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter16/Props.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Algebra.Polynomial.Eval.Defs
set_option maxHeartbeats 800000


noncomputable section

open Metric Set

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The real-valued quadratic form `φ ↦ Re⟨A φ, φ⟩` associated with an operator
`A` on a complex Hilbert space. -/
def innerQuadForm (A : H →L[ℂ] H) (φ : H) : ℝ :=
  Complex.re (@inner ℂ H _ (A φ) φ)

/-- The infimum of the numerical range of `A`: `m(A) = inf_{‖φ‖=1} Re⟨A φ, φ⟩`. -/
def numericalRangeInf (A : H →L[ℂ] H) : ℝ :=
  ⨅ φ : sphere (0 : H) 1, innerQuadForm A φ.1

/-- The supremum of the numerical range of `A`: `M(A) = sup_{‖φ‖=1} Re⟨A φ, φ⟩`. -/
def numericalRangeSup (A : H →L[ℂ] H) : ℝ :=
  ⨆ φ : sphere (0 : H) 1, innerQuadForm A φ.1

end
