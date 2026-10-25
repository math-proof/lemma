/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeRoots.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSelectedPerron.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeRoots.Part3
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFixedChargeBetheRoots_central_eq_zero_of_odd_charge
    {c : Real} (hc : 2 < c) {r : Nat} (hr : Odd r) (k : Nat) :
    sixVertexFixedChargeBetheRoots hc r k
      (sixVertexFixedChargeBetheCentralIndex r k) = 0 := by
  let i := sixVertexFixedChargeBetheCentralIndex r k
  have hi : i.rev = i := by
    apply Fin.ext
    simp only [Fin.rev, Fin.val_mk]
    dsimp [i, sixVertexFixedChargeBetheCentralIndex]
    rcases hr with ⟨s, rfl⟩
    rw [sixVertexFixedChargeBetheParticleCount_eq]
    omega
  have hsymm := (sixVertexFixedChargeBetheRoots_mem_open hc r k).2.1 i
  rw [hi] at hsymm
  linarith

theorem sixVertexFixedChargeBetheRoots_central_phase_eq_one_of_odd_charge
    {c : Real} (hc : 2 < c) {r : Nat} (hr : Odd r) (k : Nat) :
    sixVertexBethePhase (sixVertexFixedChargeBetheRoots hc r k
      (sixVertexFixedChargeBetheCentralIndex r k)) = 1 := by
  rw [sixVertexFixedChargeBetheRoots_central_eq_zero_of_odd_charge hc hr k]
  simp [sixVertexBethePhase]

end
end StatMech.FrontierD
