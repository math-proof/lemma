/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/CoordinateExamples.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Data.Matrix.Block
import Def.v1.Atlas.Buildings.code.GeometricAlgebra.CoordinateExamples.Part2
open Matrix


namespace CoordinateExamples

/-- Combinatorial data for a standard parabolic subgroup of `GL(n)`: a list of
positive block sizes whose sum is at most `n`, used to record the dimensions of
a partial flag of subspaces. -/
structure StandardParabolicData (n : ℕ) where
  sizes : List ℕ
  sizes_pos : ∀ s ∈ sizes, 0 < s
  sizes_sum : sizes.sum ≤ n

end CoordinateExamples
