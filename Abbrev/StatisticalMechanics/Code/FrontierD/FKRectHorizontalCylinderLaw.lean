module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCutPushforward.Part2
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCutFreeLaw.Part4
open scoped BigOperators
open Finset SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderLaw.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

open StatMech


abbrev FKRectHorizontalCutClosedConfig (R : FKRectTorus) :=
  {omega : R.Configuration //
    FKRectHorizontalCutClosedConfiguration R omega}

end
end StatMech.FrontierD
