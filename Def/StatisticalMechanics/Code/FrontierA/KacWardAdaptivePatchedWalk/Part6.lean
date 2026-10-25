/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptivePatchedWalk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.KacWardRawNonbacktrackingSimple
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptivePatchedWalk.Part3


namespace StatMech.FrontierA

open Set

noncomputable def KWAdaptivePatchedData.vertex
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon) :
    Fin (n * (2 * (M + 1))) → ℂ :=
  fun j ↦ patch.localVertex (finProdFinEquiv.symm j).1
    (finProdFinEquiv.symm j).2

end StatMech.FrontierA
