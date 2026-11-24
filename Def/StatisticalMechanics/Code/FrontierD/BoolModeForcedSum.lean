module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopTurningFiber.Part4
open Finset


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/BoolModeForcedSum.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def forcedBoolModeSum {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (S : Finset alpha) (forced : alpha -> Bool)
    (f : alpha -> Bool -> Real) : Real :=
  ∑ mode : alpha -> Bool,
    if forall x, x ∈ S -> mode x = forced x then
      ∏ x, f x (mode x)
    else 0


end
end StatMech.FrontierD
