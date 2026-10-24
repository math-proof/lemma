/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Def_4_7.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Data.Real.StarOrdered

open Matrix Real

noncomputable section

/-- **Definition 4.7** (Spiked covariance model). The matrix `S` follows the spiked
covariance model with spike strength `θ > 0` and unit spike direction `v` if
$\Sigma = \theta v v^\top + I_d$. -/
def IsSpikedCovariance {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) (θ : ℝ)
    (v : EuclideanSpace ℝ (Fin d)) : Prop :=
  0 < θ ∧ ‖v‖ = 1 ∧ S = θ • (vecMulVec v v) + (1 : Matrix (Fin d) (Fin d) ℝ)

/-- The principal angle between two vectors `u` and `v`, defined as
$\arccos(|\langle u, v\rangle|)$ — always in $[0, \pi/2]$. -/
noncomputable def principalAngle {d : ℕ}
    (u v : EuclideanSpace ℝ (Fin d)) : ℝ :=
  arccos |@inner ℝ _ _ u v|
