/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/FiniteNonnegativeMatrixRate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Abbrev.StatisticalMechanics.Code.Foundations.FiniteNonnegativeMatrixRate
open Finset Matrix Filter Topology
open scoped Matrix.Norms.Operator NNReal


namespace StatMech

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable instance (A : Matrix α α ℝ) (start : α) :
    DecidablePred (MatrixPositiveReachable A start) := Classical.decPred _

noncomputable instance (A : Matrix α α ℝ) (start : α) :
    DecidableEq (MatrixPositiveReachableState A start) := Classical.decEq _

end
end StatMech
