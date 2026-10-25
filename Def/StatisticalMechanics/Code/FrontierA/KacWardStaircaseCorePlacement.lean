/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseCorePlacement.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardStaircaseEndpointPatch
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardCoreTubes


namespace StatMech.FrontierA

open scoped NNReal Convex

open Set

def KWEndpointInteriorMeshWithin
    {n M : ℕ} [NeZero n]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := M + 2) polygon) (r : ℝ≥0) : Prop :=
  ∀ i : Fin n, ∀ k : Fin (M + 2), k ≠ 0 → k ≠ Fin.last (M + 1) →
    (data.parameter i k.succ - data.parameter i k.castSucc) *
      ‖polygon.edgeVector i‖ < r

end StatMech.FrontierA
