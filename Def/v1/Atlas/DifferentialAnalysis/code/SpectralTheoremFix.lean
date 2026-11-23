/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SpectralTheoremFix.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.Rayleigh
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Class.v1.Atlas.DifferentialAnalysis.code.HilbertSpace
public import Theorem.Real.Atlas.v1.DifferentialAnalysis.code.HilbertSpace

@[expose] public section

noncomputable section

open scoped ComplexInnerProductSpace

namespace SpectralTheorem

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The infimum of the Rayleigh quotient of a continuous linear operator `T` over nonzero
vectors. For self-adjoint `T`, this is the lower endpoint of `spectrum ℝ T`. -/
def rayleighInf (T : H →L[ℂ] H) : ℝ :=
  ⨅ x : { x : H // x ≠ 0 }, T.rayleighQuotient x

/-- The supremum of the Rayleigh quotient of a continuous linear operator `T` over nonzero
vectors. For self-adjoint `T`, this is the upper endpoint of `spectrum ℝ T`. -/
def rayleighSup (T : H →L[ℂ] H) : ℝ :=
  ⨆ x : { x : H // x ≠ 0 }, T.rayleighQuotient x

end SpectralTheorem
end
