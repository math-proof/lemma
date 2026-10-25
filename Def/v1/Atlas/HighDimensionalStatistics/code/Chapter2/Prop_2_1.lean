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
import Theorem.v1.Atlas.HighDimensionalStatistics.code.Chapter2.Prop_2_1.Part2
open Matrix


namespace LeastSquares

/-- The Moore–Penrose pseudoinverse `A†` of a real square matrix `A`, obtained by choice
from `exists_moorePenrosePseudoinverse`. -/
noncomputable def moorePenrosePseudoinverse {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  (exists_moorePenrosePseudoinverse A).choose

end LeastSquares
