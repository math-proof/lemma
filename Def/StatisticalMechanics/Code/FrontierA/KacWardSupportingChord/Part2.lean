/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardSupportingChord.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardExtremeVertex
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardHalfPlaneSegment
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardSupportingChord.Part2


namespace StatMech.FrontierA

def KWFiniteSimplePolygon.VertexZeroTwoStrictlyOneSided
    {m : ℕ} (polygon : KWFiniteSimplePolygon (m + 3)) : Prop :=
  (∀ k : Fin (m + 3), k ≠ 0 → k ≠ 2 →
      0 < kwComplexCross (polygon.vertex 2 - polygon.vertex 0)
        (polygon.vertex k - polygon.vertex 0)) ∨
    (∀ k : Fin (m + 3), k ≠ 0 → k ≠ 2 →
      kwComplexCross (polygon.vertex 2 - polygon.vertex 0)
        (polygon.vertex k - polygon.vertex 0) < 0)


end StatMech.FrontierA
