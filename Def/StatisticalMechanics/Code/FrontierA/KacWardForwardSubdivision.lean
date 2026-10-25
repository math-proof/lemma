/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardForwardSubdivision.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptivePatchedWalk.Part4


namespace StatMech.FrontierA

open scoped Convex

open Set


def KWRawTurnAdmissible
    {n : ℕ} [NeZero n] (vertex : Fin n → ℂ) (i : Fin n) : Prop :=
  kwComplexCross (kwRawEdge vertex i) (kwRawEdge vertex (i + 1)) ≠ 0 ∨
    ∃ r : ℝ, 0 < r ∧
      kwRawEdge vertex (i + 1) = r * kwRawEdge vertex i

end StatMech.FrontierA
