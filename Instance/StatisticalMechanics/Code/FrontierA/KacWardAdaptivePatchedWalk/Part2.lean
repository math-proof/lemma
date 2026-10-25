/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptivePatchedWalk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.KacWardRawNonbacktrackingSimple
import Def.StatisticalMechanics.Code.FrontierA.KacWardAdaptivePatchedWalk.Part3


namespace StatMech.FrontierA

open Set

noncomputable instance KWAdaptivePatchedData.sliceUsesVerticalFirst_decidable
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q : Fin M) : Decidable (patch.sliceUsesVerticalFirst i q) :=
  Classical.dec _


end StatMech.FrontierA
