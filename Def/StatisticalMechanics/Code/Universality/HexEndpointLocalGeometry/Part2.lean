module
public import Theorem.StatisticalMechanics.Code.Universality.HexEndpointVertex.Part14
public import Theorem.StatisticalMechanics.Code.Universality.HexBrickUmlaufsatz.Part4
public import Theorem.StatisticalMechanics.Code.Universality.HexEndpointLocalGeometry.Part3


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointLocalGeometry.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open Complex Function HexWalk

noncomputable section

def hexEndpointLoopPartner : List ℤ → List ℤ
  | [] => []
  | t :: tail => (-t) :: loopReverse tail

end
end StatMech.Universality
