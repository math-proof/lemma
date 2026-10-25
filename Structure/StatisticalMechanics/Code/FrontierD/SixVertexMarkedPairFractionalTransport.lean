/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairFractionalTransport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairSwitchInterface.Part3
import Instance.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairFractionalTransport
open Finset Matrix Polynomial


namespace StatMech.FrontierD

noncomputable section

structure FiniteFractionalTransport
    (Source Target : Type*) [Fintype Source] [Fintype Target]
    (sourceMass : Source -> Real) (targetCapacity : Target -> Real) where
  flow : Source -> Target -> Real
  flow_nonneg : forall source target, 0 <= flow source target
  row_sum : forall source, (∑ target, flow source target) = sourceMass source
  column_le : forall target,
    (∑ source, flow source target) <= targetCapacity target


end
end StatMech.FrontierD
