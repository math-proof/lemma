/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairFractionalTransport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairSwitchInterface.Part3
import Structure.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairFractionalTransport
open Finset Matrix Polynomial


namespace StatMech.FrontierD

noncomputable section

theorem FiniteFractionalTransport.total_le
    {Source Target : Type*} [Fintype Source] [Fintype Target]
    {sourceMass : Source -> Real} {targetCapacity : Target -> Real}
    (transport : FiniteFractionalTransport
      Source Target sourceMass targetCapacity) :
    (∑ source, sourceMass source) <= ∑ target, targetCapacity target := by
  calc
    (∑ source, sourceMass source) =
        ∑ source, ∑ target, transport.flow source target := by
      apply Finset.sum_congr rfl
      intro source hsource
      exact (transport.row_sum source).symm
    _ = ∑ target, ∑ source, transport.flow source target :=
      Finset.sum_comm
    _ <= ∑ target, targetCapacity target :=
      Finset.sum_le_sum fun target htarget => transport.column_le target


end
end StatMech.FrontierD
