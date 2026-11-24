module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusSquareDevelopment.Part12
public import Theorem.StatisticalMechanics.Code.FrontierD.IntegralSquareTorusIntersection.Part9
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusSquareCoverIntersection.Part5
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareCoverIntersection.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

open StatMech.Onsager

noncomputable section

def fkRectSquareCoverSide (R : FKRectTorus) : Nat :=
  R.width * R.height

end
end StatMech.FrontierD
