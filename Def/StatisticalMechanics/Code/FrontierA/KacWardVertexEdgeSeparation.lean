/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardVertexEdgeSeparation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearSeparation.Part2


namespace StatMech.FrontierA

open scoped NNReal ENNReal Convex

open Set


def KWVertexEdgeNonincident {n : ℕ} [NeZero n] (v j : Fin n) : Prop :=
  v ≠ j ∧ v ≠ j + 1

end StatMech.FrontierA
