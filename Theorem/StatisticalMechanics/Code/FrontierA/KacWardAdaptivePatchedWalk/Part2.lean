/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptivePatchedWalk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.KacWardRawNonbacktrackingSimple
import Def.StatisticalMechanics.Code.FrontierA.KacWardAdaptivePatchedWalk.Part4


namespace StatMech.FrontierA

open Set

@[simp] theorem KWAdaptivePatchedData.pathBase_castSucc
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q : Fin M) :
    patch.pathBase i q.castSucc =
      patch.data.base i q.succ.castSucc.castSucc := by
  simp [KWAdaptivePatchedData.pathBase]

@[simp] theorem KWAdaptivePatchedData.pathBase_last
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) :
    patch.pathBase i (Fin.last M) = patch.incomingPort i := by
  simp [KWAdaptivePatchedData.pathBase]

@[simp] theorem KWAdaptivePatchedData.pathCorner_castSucc
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q : Fin M) :
    patch.pathCorner i q.castSucc =
      patch.middleCorner i q := by
  simp [KWAdaptivePatchedData.pathCorner]

@[simp] theorem KWAdaptivePatchedData.pathCorner_last
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) :
    patch.pathCorner i (Fin.last M) = patch.connectorCorner (i + 1) := by
  simp [KWAdaptivePatchedData.pathCorner]

end StatMech.FrontierA
