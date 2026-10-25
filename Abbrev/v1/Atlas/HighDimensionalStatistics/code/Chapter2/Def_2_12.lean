/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter2/Def_2_12.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter2.Def_2_12
open Finset Matrix BigOperators


namespace Rigollet

/-- Alias for `IsBICEstimator`, emphasising the squared-`ℓ_2` data-fitting term. -/
abbrev IsBICEstimatorL2 {n d : ℕ} (X : Matrix (Fin n) (Fin d) ℝ)
    (Y : Fin n → ℝ) (τ : ℝ) (θhat : Fin d → ℝ) : Prop :=
  IsBICEstimator X Y τ θhat

/-- Alias for `IsLassoEstimator`, emphasising the squared-`ℓ_2` data-fitting term. -/
abbrev IsLassoEstimatorL2 {n d : ℕ} (X : Matrix (Fin n) (Fin d) ℝ)
    (Y : Fin n → ℝ) (τ : ℝ) (θhat : Fin d → ℝ) : Prop :=
  IsLassoEstimator X Y τ θhat

end Rigollet
