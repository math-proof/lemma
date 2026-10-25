/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeRoots.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSelectedPerron.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeRoots
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem sixVertexFixedChargeBetheParticleCount_eq (r k : Nat) :
    sixVertexFixedChargeBetheParticleCount r k = r + 2 * (k + 1) := by
  unfold sixVertexFixedChargeBetheParticleCount sixVertexFourWidth
  omega

theorem sixVertexFixedChargeBetheParticleCount_pos (r k : Nat) :
    0 < sixVertexFixedChargeBetheParticleCount r k := by
  rw [sixVertexFixedChargeBetheParticleCount_eq]
  omega

theorem sixVertexFixedChargeBetheParticleCount_twice_le (r k : Nat) :
    2 * sixVertexFixedChargeBetheParticleCount r k <=
      sixVertexFourWidth r k := by
  rw [sixVertexFixedChargeBetheParticleCount_eq]
  unfold sixVertexFourWidth
  omega


end
end StatMech.FrontierD
