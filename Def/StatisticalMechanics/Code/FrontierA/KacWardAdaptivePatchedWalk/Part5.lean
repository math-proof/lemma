/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptivePatchedWalk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.KacWardRawNonbacktrackingSimple
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptivePatchedWalk.Part2


namespace StatMech.FrontierA

open Set

noncomputable def KWAdaptivePatchedData.localVertex
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (l : Fin (2 * (M + 1))) : ℂ :=
  if l.val % 2 = 0 then
    patch.pathBase i (kwStairSliceIndex l)
  else
    patch.pathCorner i (kwStairSliceIndex l)

end StatMech.FrontierA
