/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealWalk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveConnectorScales
import Def.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveIdealWalk.Part2


namespace StatMech.FrontierA

@[simp] theorem KWAdaptivePatchedData.idealLocalVertex_even
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (k : Fin (M + 1)) :
    patch.idealLocalVertex i (kwStairEvenLocal k) = patch.pathBase i k := by
  simp [KWAdaptivePatchedData.idealLocalVertex, kwStairSliceIndex_even]

@[simp] theorem KWAdaptivePatchedData.idealLocalVertex_odd
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (k : Fin (M + 1)) :
    patch.idealLocalVertex i (kwStairOddLocal k) =
      patch.idealPathCorner i k := by
  simp [KWAdaptivePatchedData.idealLocalVertex, kwStairSliceIndex_odd]

end StatMech.FrontierA
