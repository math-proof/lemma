/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCentralSectorDominance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexWidthFreeEnergy.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexParticleHole.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePerronContinuation.Part13
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexCoordinateBetheOne.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexCentralSectorDominance
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

def SixVertexStrictLowerHalfDominance (N : Nat) (c : Real) : Prop :=
  ∀ n : Nat, (hn0 : 0 < n) -> (hn : n < N / 2) ->
    sixVertexSectorTopEigenvalue N n
        (hn.le.trans (Nat.div_le_self N 2)) c <=
      sixVertexSectorTopEigenvalue N (N / 2)
        (Nat.div_le_self N 2) c


def SixVertexStrictLowerHalfDominanceAboveOne (N : Nat) (c : Real) : Prop :=
  ∀ n : Nat, (hn1 : 1 < n) -> (hn : n < N / 2) ->
    sixVertexSectorTopEigenvalue N n
        (hn.le.trans (Nat.div_le_self N 2)) c <=
      sixVertexSectorTopEigenvalue N (N / 2)
        (Nat.div_le_self N 2) c


end
end StatMech.FrontierD
