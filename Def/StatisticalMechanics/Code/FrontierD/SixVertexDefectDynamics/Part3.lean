/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDefectDynamics.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePerronContinuation.Part13
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDefectDynamics.Part2
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexSectorDefectState
    {N n : Nat} (x : SixVertexSector N n)
    (hx : SixVertexSectorNoAdjacent x) (hn : 0 < n) :
    SixVertexDefectState n (N - 2 * n) :=
  ⟨sixVertexSectorGapDefects x, sum_sixVertexSectorGapDefects x hx hn⟩


def sixVertexFixedChargeSectorDefectState
    (r k : Nat)
    (x : SixVertexSector (sixVertexFourWidth r k)
      (sixVertexFixedChargeBetheParticleCount r k))
    (hx : SixVertexSectorNoAdjacent x) :
    SixVertexDefectState (sixVertexFixedChargeBetheParticleCount r k) (2 * r) :=
  ⟨sixVertexSectorGapDefects x, by
    rw [sum_sixVertexSectorGapDefects x hx,
      sixVertexFixedChargeBetheParticleCount_eq]
    · unfold sixVertexFourWidth
      omega
    · exact sixVertexFixedChargeBetheParticleCount_pos r k⟩

end
end StatMech.FrontierD
