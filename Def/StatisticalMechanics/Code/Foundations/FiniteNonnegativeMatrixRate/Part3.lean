/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/FiniteNonnegativeMatrixRate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Instance.StatisticalMechanics.Code.Foundations.FiniteNonnegativeMatrixRate.Part2
open Finset Matrix Filter Topology
open scoped Matrix.Norms.Operator NNReal


namespace StatMech

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

def matrixPositiveReachableRestriction (A : Matrix α α ℝ) (start : α) :
    Matrix (MatrixPositiveReachableState A start)
      (MatrixPositiveReachableState A start) ℝ :=
  fun i j => A i.1 j.1

end
end StatMech
