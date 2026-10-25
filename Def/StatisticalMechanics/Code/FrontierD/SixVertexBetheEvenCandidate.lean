/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEvenCandidate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeRoots.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheEvenCandidate
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexFixedEvenChargeBetheRoots
    {c : Real} (hc : 2 < c) (s k : Nat) :
    Fin ((s + k + 1) + (s + k + 1)) -> Real :=
  fun i => sixVertexFixedChargeBetheRoots hc (2 * s) k
    (Fin.cast (sixVertexFixedEvenChargeBetheParticleCount_eq s k).symm i)

def sixVertexFixedEvenPositiveBetheRoots
    {c : Real} (hc : 2 < c) (s k : Nat) : Fin (s + k + 1) -> Real :=
  fun j => sixVertexFixedEvenChargeBetheRoots hc s k
    (Fin.natAdd (s + k + 1) j)

end
end StatMech.FrontierD
