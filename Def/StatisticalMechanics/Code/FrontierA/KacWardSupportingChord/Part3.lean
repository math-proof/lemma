/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardSupportingChord.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardExtremeVertex
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardHalfPlaneSegment
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardSupportingChord.Part3


namespace StatMech.FrontierA

def KWFiniteSimplePolygon.VertexOneStrictlySeparated
    {m : ℕ} (polygon : KWFiniteSimplePolygon (m + 3)) : Prop :=
  let side := fun k : Fin (m + 3) ↦
    kwComplexCross (polygon.vertex 2 - polygon.vertex 0)
      (polygon.vertex k - polygon.vertex 0)
  (0 < side 1 ∧ ∀ k, k ≠ 0 → k ≠ 1 → k ≠ 2 → side k < 0) ∨
    (side 1 < 0 ∧ ∀ k, k ≠ 0 → k ≠ 1 → k ≠ 2 → 0 < side k)


end StatMech.FrontierA
