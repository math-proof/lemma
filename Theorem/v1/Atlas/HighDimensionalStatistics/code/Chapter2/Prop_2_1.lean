/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter2/Prop_2_1.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.Data.Real.StarOrdered
public import Mathlib.Analysis.Matrix.Spectrum
open Matrix

public section

namespace LeastSquares

/-- For a real square matrix, the transpose equals the star (since conjugation is trivial on `ℝ`). -/
lemma transpose_eq_star_real {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℝ) : X.transpose = star X := by
  rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]

end LeastSquares
