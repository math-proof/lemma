module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheAnisotropyRoots.Part4
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeRoots.Part3
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeAnisotropyRoots
open Finset Filter Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeAnisotropyRoots.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def sixVertexFixedChargeBetheRootAt (r k : Nat)
    (j : Fin (sixVertexFixedChargeBetheParticleCount r k)) (c : Real) : Real :=
  if hc : 2 < c then sixVertexFixedChargeBetheRoots hc r k j else 0

end
end StatMech.FrontierD
