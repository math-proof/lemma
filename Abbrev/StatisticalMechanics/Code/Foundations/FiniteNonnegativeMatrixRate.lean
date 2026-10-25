/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/FiniteNonnegativeMatrixRate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.StatisticalMechanics.Code.Foundations.FiniteNonnegativeMatrixRate
open Finset Matrix Filter Topology
open scoped Matrix.Norms.Operator NNReal


namespace StatMech

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

abbrev MatrixPositiveReachableState (A : Matrix α α ℝ) (start : α) :=
  {target : α // MatrixPositiveReachable A start target}

end
end StatMech
