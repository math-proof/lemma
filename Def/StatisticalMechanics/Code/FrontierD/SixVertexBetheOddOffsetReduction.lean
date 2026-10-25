/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddOffsetReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheZeroPhase.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierEvaluation.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOddOffsetReduction
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexOddChargeBetheCandidateLogRatio
    {c : Real} (hc : 2 < c) (r k : Nat) : Real :=
  Real.log (sixVertexFixedOddChargeBetheEigenvalueValue hc r k) -
    Real.log (sixVertexSymmetricBetheEigenvalueValue c
      (sixVertexPositiveHalfBetheRoots hc (r + k)))


end
end StatMech.FrontierD
