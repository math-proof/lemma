module
public import Def.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveConnectorScales
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveIdealWalk


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealWalk.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

noncomputable def KWAdaptivePatchedData.idealLocalVertex
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (l : Fin (2 * (M + 1))) : ℂ :=
  if l.val % 2 = 0 then
    patch.pathBase i (kwStairSliceIndex l)
  else
    patch.idealPathCorner i (kwStairSliceIndex l)

end StatMech.FrontierA
