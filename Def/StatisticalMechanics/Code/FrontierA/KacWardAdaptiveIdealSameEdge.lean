/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealSameEdge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveConnectorClosedSeparation
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveIdealSameEdge


namespace StatMech.FrontierA

open Set

noncomputable def KWAdaptivePatchedData.idealMidParameter
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q : Fin M) : ℝ :=
  (patch.data.parameter i q.succ.castSucc.castSucc +
    patch.data.parameter i q.succ.castSucc.succ) / 2

end StatMech.FrontierA
