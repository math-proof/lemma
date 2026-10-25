/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealMiddleGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveConnectorClosedSeparation


namespace StatMech.FrontierA

open scoped Convex

open Set

def KWAdaptivePatchedData.idealMiddleClosedEdge
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q : Fin M) (even : Bool) : Set ℂ :=
  if even then
    kwRawClosedEdge patch.idealVertex (kwStairEvenIndex i q.castSucc)
  else
    kwRawClosedEdge patch.idealVertex (kwStairOddIndex i q.castSucc)

end StatMech.FrontierA
