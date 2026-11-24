module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCutPushforward.Part2
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCutFreeLaw.Part4
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderLaw.Part3
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


def fkRectHorizontalCutClosedReducedEventWeight
    (R : FKRectTorus) (q : Real) (A : Set R.Configuration) : Real :=
  ∑ omega : FKRectHorizontalCutClosedConfig R,
    A.indicator (fun eta => fkRectCriticalReducedWeight R q eta) omega.1


def fkRectHorizontalCutClosedReducedZ
    (R : FKRectTorus) (q : Real) : Real :=
  ∑ omega : FKRectHorizontalCutClosedConfig R,
    fkRectCriticalReducedWeight R q omega.1

end
end StatMech.FrontierD
