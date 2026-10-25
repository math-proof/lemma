/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealWalk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveConnectorScales
import Def.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveIdealWalk


namespace StatMech.FrontierA

@[simp] theorem KWAdaptivePatchedData.idealPathCorner_castSucc
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q : Fin M) :
    patch.idealPathCorner i q.castSucc = patch.idealMiddleCorner i q := by
  simp [KWAdaptivePatchedData.idealPathCorner]

@[simp] theorem KWAdaptivePatchedData.idealPathCorner_last
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) :
    patch.idealPathCorner i (Fin.last M) = patch.connectorCorner (i + 1) := by
  simp [KWAdaptivePatchedData.idealPathCorner]

end StatMech.FrontierA
