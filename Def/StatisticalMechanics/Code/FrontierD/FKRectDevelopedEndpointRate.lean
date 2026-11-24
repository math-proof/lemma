module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedEndpointSpan
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
open Filter Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedEndpointRate.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def fkRectDevelopedReflectedEndpointLowerOf
    (crossingFloor : Real) (n : Nat) : Real :=
  (crossingFloor / (((3 * n + 1) ^ 2 : Nat) : Real)) ^ 2

end
end StatMech.FrontierD
