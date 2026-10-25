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
open MeasureTheory Real Matrix Equiv Finset


namespace Approximation

def IsApprox {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Q' : Ω → ℝ) (Q ε δ : ℝ) : Prop :=
  μ {ω | |Q' ω - Q| ≤ ε * Q} ≥ ENNReal.ofReal (1 - δ)

def IsPolyTime (runtime : ℕ → ℝ → ℝ → ℕ) : Prop :=
  ∃ (c k : ℕ), ∀ (n : ℕ) (ε δ : ℝ), 0 < ε → 0 < δ →
    (runtime n ε δ : ℝ) ≤ ↑c * (↑n + 1 / ε + Real.log (1 / δ)) ^ k

end Approximation
