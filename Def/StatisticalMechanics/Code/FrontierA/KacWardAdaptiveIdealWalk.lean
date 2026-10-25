/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealWalk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveConnectorScales


namespace StatMech.FrontierA

noncomputable def KWAdaptivePatchedData.idealMiddleCorner
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q : Fin M) : ℂ :=
  patch.data.base i q.succ.castSucc.castSucc +
    (1 / 2 : ℝ) *
      (patch.data.base i q.succ.castSucc.succ -
        patch.data.base i q.succ.castSucc.castSucc)

noncomputable def KWAdaptivePatchedData.idealPathCorner
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (k : Fin (M + 1)) : ℂ :=
  Fin.lastCases (patch.connectorCorner (i + 1))
    (fun q : Fin M ↦ patch.idealMiddleCorner i q) k

end StatMech.FrontierA
