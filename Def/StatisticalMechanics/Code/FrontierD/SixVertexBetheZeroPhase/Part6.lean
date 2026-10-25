/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhase.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeRoots.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexCoordinateBetheOne.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheZeroPhase.Part6
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexFixedOddChargeBetheEigenvalueValue
    {c : Real} (hc : 2 < c) (r k : Nat) : Real :=
  sixVertexZeroPhaseBetheEigenvalueValue c (sixVertexFourWidth r k)
    (sixVertexFixedChargeBetheRoots hc r k)
    (sixVertexFixedChargeBetheCentralIndex r k)

def sixVertexFixedOddChargeBetheEigenvalueCandidate
    {c : Real} (hc : 2 < c) (r k : Nat) : Complex :=
  sixVertexZeroPhaseBetheEigenvalueCandidate c (sixVertexFourWidth r k)
    (sixVertexFixedChargeBetheRoots hc r k)
    (sixVertexFixedChargeBetheCentralIndex r k)

end
end StatMech.FrontierD
