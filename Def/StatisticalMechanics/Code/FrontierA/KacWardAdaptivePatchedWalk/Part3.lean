module
public import Def.StatisticalMechanics.Code.FrontierA.KacWardRawNonbacktrackingSimple
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptivePatchedWalk


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptivePatchedWalk.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open Set

def KWAdaptivePatchedData.sliceUsesVerticalFirst
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
  (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q : Fin M) : Prop :=
  (q = 0 ∧ patch.connectorUsesVerticalFirst i) ∨
    (q = patch.lastMiddleIndex ∧
      patch.connectorUsesVerticalFirst (i + 1))

end StatMech.FrontierA
