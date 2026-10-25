/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter2/Prop_2_1.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Data.Real.StarOrdered
import Mathlib.Analysis.Matrix.Spectrum
import Theorem.v1.Atlas.HighDimensionalStatistics.code.Chapter2.Prop_2_1
open Matrix


namespace LeastSquares

/-- Predicate stating that `B` is the Moore–Penrose pseudoinverse of `A`. It encodes the
four classical Penrose conditions: `A B A = A`, `B A B = B`, `A B` is symmetric, and
`B A` is symmetric. -/
structure IsMoorePenrosePseudoinverse {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℝ) (B : Matrix n m ℝ) : Prop where
  mul_pinv_mul : A * B * A = A
  pinv_mul_pinv : B * A * B = B
  mul_pinv_symmetric : (A * B).transpose = A * B
  pinv_mul_symmetric : (B * A).transpose = B * A

end LeastSquares
