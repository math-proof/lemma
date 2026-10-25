/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveSameEdgeMiddle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardVertexCoreSeparation
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveSameEdgeMiddle


namespace StatMech.FrontierA

open scoped Convex

open Set

def kwAdaptiveMiddleIndex
    {n M : ℕ} [NeZero n] [NeZero M]
    (i : Fin n) (q : Fin M) (even : Bool) :
    Fin (n * (2 * (M + 1))) :=
  if even then kwStairEvenIndex i q.castSucc
  else kwStairOddIndex i q.castSucc

def KWAdaptivePatchedData.middleClosedEdge
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q : Fin M) (even : Bool) : Set ℂ :=
  kwRawClosedEdge patch.vertex (kwAdaptiveMiddleIndex i q even)

end StatMech.FrontierA
