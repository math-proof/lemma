/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/Intrinsic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.DifferentialGeometry.code.Hypersurfaces
import Lemma.Real.Atlas.v1.DifferentialGeometry.code.Hypersurfaces
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Tactic.NoncommRing
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Def.v1.Atlas.DifferentialGeometry.code.Intrinsic


noncomputable section

open Matrix Finset BigOperators

variable {n : ℕ}

namespace ChristoffelSymbols

namespace ChristoffelFromMetric

open ChristoffelSymbols

structure IsMovingBasis (patch : HypersurfacePatch n)
    (X : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) : Prop where
  smooth : ContDiffOn ℝ ⊤ X patch.domain
  invertible : ∀ x ∈ patch.domain, IsUnit (X x)

structure IsMovingFrame (patch : HypersurfacePatch n)
    (X : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) : Prop extends IsMovingBasis patch X where
  orthonormal : ∀ x ∈ patch.domain,
    (X x)ᵀ * firstFundamentalForm patch x * (X x) = 1

end ChristoffelFromMetric
end ChristoffelSymbols
end
