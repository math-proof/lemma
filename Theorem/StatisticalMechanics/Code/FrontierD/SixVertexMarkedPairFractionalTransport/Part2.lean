/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairFractionalTransport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairSwitchInterface.Part3
import Structure.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairFractionalTransport.Part2
open Finset Matrix Polynomial


namespace StatMech.FrontierD

noncomputable section

theorem FiniteFractionalTransportOn.total_le
    {Source Target : Type*} [Fintype Source] [Fintype Target]
    {sourceMass : Source -> Real} {targetCapacity : Target -> Real}
    {related : Source -> Target -> Prop}
    (transport : FiniteFractionalTransportOn
      Source Target sourceMass targetCapacity related) :
    (∑ source, sourceMass source) <= ∑ target, targetCapacity target :=
  transport.toFiniteFractionalTransport.total_le


end
end StatMech.FrontierD
