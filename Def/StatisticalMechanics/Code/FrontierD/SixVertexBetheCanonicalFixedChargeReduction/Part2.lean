/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedChargeReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronClosed
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheEventualOddPerron
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheEvenCandidate.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedEvenPerronBranch.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedOddPerronBranch.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedChargeReduction
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexCanonicalFixedChargeBetheCandidateLogRatio
    {c : Real} (hc : 2 < c) (r k : Nat) : Real :=
  Real.log (sixVertexFixedChargeBetheEigenvalueValue hc r k) -
    Real.log (sixVertexSymmetricBetheEigenvalueValue c
      (sixVertexCanonicalDensityPerronPositiveHalfRoots hc (r + k)))


def SixVertexCanonicalFixedChargeBetheCandidateMatchesOffsetFourier
    {c : Real} (hc : 2 < c) (r : Nat) : Prop :=
  Tendsto (fun k =>
      sixVertexCanonicalFixedChargeBetheCandidateLogRatio hc r k +
        (r : Real) * sixVertexOffsetFourierPartialSum
          (sixVertexAntiferroelectricLambda c) k)
    atTop (nhds 0)


end
end StatMech.FrontierD
