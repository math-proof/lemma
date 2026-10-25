/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Problem_4_3.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter4.Def_4_1.Part3
import Mathlib.Order.Bounds.Basic
open Matrix Real Finset MeasureTheory


noncomputable section

namespace Chapter4.Problem43

/-- Squared Frobenius norm of a `Fin d × Fin T` real matrix. -/
def frobSqNorm {d T : ℕ} (A : Matrix (Fin d) (Fin T) ℝ) : ℝ :=
  ∑ i, ∑ j, (A i j) ^ 2

/-- Nuclear norm computed from a given SVD: the sum of singular values. -/
def nuclearNorm {d T : ℕ} (S : SVD d T) : ℝ :=
  ∑ j : Fin S.r, S.σval j

/-- Soft thresholding: `(x - τ)_+`, the positive part of `x - τ`. -/
def softThreshold (x τ : ℝ) : ℝ := max (x - τ) 0

/-- Apply soft thresholding to the singular values of `S`, producing the soft-thresholded
matrix $\sum_j (\sigma_j - \tau)_+\, u_j v_j^\top$. -/
def softThreshMatrix {d T : ℕ} (S : SVD d T) (τ : ℝ) : Matrix (Fin d) (Fin T) ℝ :=
  ∑ j : Fin S.r, softThreshold (S.σval j) τ • vecMulVec (S.u j) (S.v j)

/-- `(M, S)` is a minimizer of the nuclear-norm penalized least squares problem
$\arg\min_M \|Y - M\|_F^2/n + \tau \|M\|_*$. -/
def IsNuclearNormMinimizer {d T : ℕ} (Y M : Matrix (Fin d) (Fin T) ℝ)
    (S : SVD d T) (τ : ℝ) (n : ℕ) : Prop :=
  S.IsDecompOf M ∧
  ∀ (M' : Matrix (Fin d) (Fin T) ℝ) (S' : SVD d T), S'.IsDecompOf M' →
    frobSqNorm (Y - M) / n + τ * nuclearNorm S ≤
      frobSqNorm (Y - M') / n + τ * nuclearNorm S'

end Chapter4.Problem43
end
