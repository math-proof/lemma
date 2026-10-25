/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedOddCandidateAnisotropy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedEvenCandidateAnisotropy.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheZeroPhaseSingle.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedOddCandidateAnisotropy
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexFixedOddChargeBethePrefactorNormalized
    (s k : Nat) (c : Real) : Real :=
  if hc : 2 < c then
    sixVertexZeroPhaseBethePrefactor c (sixVertexFourWidth (2 * s + 1) k)
        (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k)
        (sixVertexFixedChargeBetheCentralIndex (2 * s + 1) k) /
      (c ^ 2 - 2)
  else 0

end
end StatMech.FrontierD
