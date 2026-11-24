module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCutPushforward.Part2
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCutFreeLaw.Part4
public import Abbrev.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderLaw
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


noncomputable instance instFintypeFKRectHorizontalCutClosedConfig
    (R : FKRectTorus) : Fintype (FKRectHorizontalCutClosedConfig R) := by
  unfold FKRectHorizontalCutClosedConfig
  infer_instance


end
end StatMech.FrontierD
