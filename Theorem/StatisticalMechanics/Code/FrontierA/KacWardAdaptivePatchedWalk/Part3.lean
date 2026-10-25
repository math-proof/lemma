/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptivePatchedWalk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.KacWardRawNonbacktrackingSimple
import Def.StatisticalMechanics.Code.FrontierA.KacWardAdaptivePatchedWalk.Part5


namespace StatMech.FrontierA

open Set

@[simp] theorem KWAdaptivePatchedData.localVertex_even
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (k : Fin (M + 1)) :
    patch.localVertex i (kwStairEvenLocal k) = patch.pathBase i k := by
  simp [KWAdaptivePatchedData.localVertex, kwStairSliceIndex_even]

@[simp] theorem KWAdaptivePatchedData.localVertex_odd
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (k : Fin (M + 1)) :
    patch.localVertex i (kwStairOddLocal k) = patch.pathCorner i k := by
  simp [KWAdaptivePatchedData.localVertex, kwStairSliceIndex_odd]

end StatMech.FrontierA
