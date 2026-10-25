/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDefectDynamics.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePerronContinuation.Part13
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDefectDynamics.Part3
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFixedChargeSectorDefectState_reachable_pile
    (r k : Nat)
    (x : SixVertexSector (sixVertexFourWidth r k)
      (sixVertexFixedChargeBetheParticleCount r k))
    (hx : SixVertexSectorNoAdjacent x) :
    (sixVertexDefectLowerGraph
      (sixVertexFixedChargeBetheParticleCount r k) (2 * r)).Reachable
      (sixVertexFixedChargeSectorDefectState r k x hx)
      ⟨sixVertexDefectPile
          (sixVertexFixedChargeBetheParticleCount_pos r k) (2 * r),
        sixVertexDefectPile_sum
          (sixVertexFixedChargeBetheParticleCount_pos r k) (2 * r)⟩ := by
  exact sixVertexDefectLowerGraph_reachable_pile
    (sixVertexFixedChargeBetheParticleCount_pos r k) _

end
end StatMech.FrontierD
