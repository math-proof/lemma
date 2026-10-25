/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealWalk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveConnectorScales
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveIdealWalk.Part2


namespace StatMech.FrontierA

noncomputable def KWAdaptivePatchedData.idealVertex
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon) :
    Fin (n * (2 * (M + 1))) → ℂ :=
  fun j ↦ patch.idealLocalVertex (finProdFinEquiv.symm j).1
    (finProdFinEquiv.symm j).2

end StatMech.FrontierA
