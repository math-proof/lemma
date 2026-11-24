module
public import Theorem.StatisticalMechanics.Code.Universality.HexEndpointVertex.Part14
public import Theorem.StatisticalMechanics.Code.Universality.HexBrickUmlaufsatz.Part4
public import Structure.StatisticalMechanics.Code.Universality.HexEndpointLocalGeometry.Part2


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

def HexEndpointCyclicLoopPair.piece
    {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}
    (P : HexEndpointCyclicLoopPair region a h0 v du) : Finset (List ℤ) :=
  {P.base ++ P.loopQ, P.base ++ hexEndpointLoopPartner P.loopQ}

end
end StatMech.Universality
