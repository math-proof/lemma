/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveVertexConnector.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRawSimpleFromEdges
import Def.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveVertexConnector.Part2


namespace StatMech.FrontierA

open Set


structure KWAdaptiveConnectorData (a b : ℂ) where
  corner : ℂ
  axis_corner :
    (corner = kwHVConnectorCorner a b) ∨
      (corner = kwVHConnectorCorner a b)
  corner_ne_left : corner ≠ a
  corner_ne_right : corner ≠ b
  turn_ne_zero : kwComplexCross (corner - a) (b - corner) ≠ 0
  path_disjoint_rayTails :
    Disjoint (kwConnectorOpenPath a corner b)
      (kwOpenRayTail a ∪ kwOpenRayTail b)

end StatMech.FrontierA
