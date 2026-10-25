/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/Approximation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Def.v1.Atlas.AnAlgorithmistsToolkit.code.Approximation
open MeasureTheory Real Matrix Equiv Finset


namespace Approximation

structure FPRAS where
  Ω : ℕ → ℝ → ℝ → Type*
  meas : ∀ n ε δ, MeasurableSpace (Ω n ε δ)
  μ : ∀ n ε δ, @Measure (Ω n ε δ) (meas n ε δ)
  Q : ℕ → ℝ
  estimator : ∀ n ε δ, Ω n ε δ → ℝ
  runtime : ℕ → ℝ → ℝ → ℕ
  approx : ∀ (n : ℕ) (ε δ : ℝ), 0 < ε → 0 < δ →
    @IsApprox _ (meas n ε δ) (μ n ε δ) (estimator n ε δ) (Q n) ε δ
  poly_time : IsPolyTime runtime

end Approximation
