/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEvenCandidate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeRoots.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheEvenCandidate.Part3
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexEvenChargeBetheCandidateLogRatio
    {c : Real} (hc : 2 < c) (s k : Nat) : Real :=
  Real.log (sixVertexFixedEvenChargeBetheEigenvalueValue hc s k) -
    Real.log (sixVertexSymmetricBetheEigenvalueValue c
      (sixVertexPositiveHalfBetheRoots hc (2 * s + k)))

end
end StatMech.FrontierD
