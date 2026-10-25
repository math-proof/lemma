/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptivePatchedWalk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.KacWardRawNonbacktrackingSimple
import Instance.StatisticalMechanics.Code.FrontierA.KacWardAdaptivePatchedWalk.Part2


namespace StatMech.FrontierA

open Set

noncomputable def KWAdaptivePatchedData.middleCorner
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q : Fin M) : ℂ :=
  if patch.sliceUsesVerticalFirst i q then
    patch.data.base i q.succ.castSucc.castSucc +
      (patch.data.parameter i q.succ.castSucc.succ -
        patch.data.parameter i q.succ.castSucc.castSucc) *
          kwVerticalPart (polygon.edgeVector i)
  else
    patch.data.corner i q.succ.castSucc

noncomputable def KWAdaptivePatchedData.pathCorner
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (k : Fin (M + 1)) : ℂ :=
  Fin.lastCases (patch.connectorCorner (i + 1))
    (fun q : Fin M ↦ patch.middleCorner i q) k

end StatMech.FrontierA
