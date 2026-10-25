/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddOffsetReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheZeroPhase.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierEvaluation.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOddOffsetReduction.Part2
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

def SixVertexOddChargeBethePerronIdentification
    (c : Real) (r : Nat) : Prop :=
  ∀ hc : 2 < c, ∀ k,
    sixVertexFixedOddChargeBetheEigenvalueValue hc r k =
      sixVertexLambdaAlongFour c r k


def SixVertexOddChargeBetheCandidateMatchesOffsetFourier
    {c : Real} (hc : 2 < c) (r : Nat) : Prop :=
  Tendsto (fun k => sixVertexOddChargeBetheCandidateLogRatio hc r k +
      (r : Real) * sixVertexOffsetFourierPartialSum
        (sixVertexAntiferroelectricLambda c) k)
    atTop (nhds 0)

end
end StatMech.FrontierD
