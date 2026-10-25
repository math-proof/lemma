/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeRoots.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSelectedPerron.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeRoots
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexFixedChargeBetheRoots
    {c : Real} (hc : 2 < c) (r k : Nat) :
    Fin (sixVertexFixedChargeBetheParticleCount r k) -> Real :=
  sixVertexChosenBetheSolution hc
    (sixVertexFixedChargeBetheParticleCount_twice_le r k)

end
end StatMech.FrontierD
