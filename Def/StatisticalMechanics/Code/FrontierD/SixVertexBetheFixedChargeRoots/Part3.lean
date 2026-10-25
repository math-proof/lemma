/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeRoots.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSelectedPerron.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeRoots.Part2
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexFixedChargeBetheCentralIndex (r k : Nat) :
    Fin (sixVertexFixedChargeBetheParticleCount r k) :=
  ⟨sixVertexFixedChargeBetheParticleCount r k / 2,
    Nat.div_lt_self (sixVertexFixedChargeBetheParticleCount_pos r k)
      (by omega)⟩


end
end StatMech.FrontierD
