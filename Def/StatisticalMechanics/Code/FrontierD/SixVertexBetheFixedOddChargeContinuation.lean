/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedOddChargeContinuation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOddSymmetricCovering
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeContinuationPoint
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedOddChargeContinuation
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexFixedOddChargeBetheRoots
    {c : Real} (hc : 2 < c) (s k : Nat) :
    Fin (((s + k + 1) + 1) + (s + k + 1)) → Real :=
  fun i => sixVertexFixedChargeBetheRoots hc (2 * s + 1) k
    (Fin.cast (sixVertexFixedOddChargeBetheParticleCount_eq s k).symm i)

def sixVertexFixedOddPositiveBetheRoots
    {c : Real} (hc : 2 < c) (s k : Nat) : Fin (s + k + 1) → Real :=
  fun j => sixVertexFixedOddChargeBetheRoots hc s k
    (sixVertexOddPositiveIndex (s + k + 1) j)

end
end StatMech.FrontierD
