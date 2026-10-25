/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedOddChargePerronClosed.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOddUniqueStabilitySheet
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedOddChargeContinuation.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeEventualPerron
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedEvenChargePerronClosed.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedOddChargePerronClosed
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexSelectedFixedChargeBetheEigenvalueValue
    {c : Real} (hc : 2 < c) (r k : Nat) : Real :=
  if _hr : Even r then
    sixVertexFixedEvenChargeBetheEigenvalueValue hc (r / 2) k
  else
    sixVertexFixedOddChargeBetheEigenvalueValue hc r k


end
end StatMech.FrontierD
