/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptivePatchedWalk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.KacWardRawNonbacktrackingSimple
import Instance.StatisticalMechanics.Code.FrontierA.KacWardAdaptivePatchedWalk


namespace StatMech.FrontierA

open Set

def KWAdaptivePatchedData.lastMiddleIndex
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon) : Fin M :=
  ⟨M - 1, by have := patch.hM; omega⟩

end StatMech.FrontierA
