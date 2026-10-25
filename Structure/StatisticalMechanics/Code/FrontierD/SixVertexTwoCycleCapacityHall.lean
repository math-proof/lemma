/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexTwoCycleCapacityHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairedBranchResidualHall.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexTwoCycleCapacityHall
open Finset


namespace StatMech.FrontierD

noncomputable section

structure FiniteKeyCapacityTransport
    (Key : Type*) [Fintype Key]
    (sourceCapacity targetCapacity : Key -> Nat)
    (related : Key -> Key -> Prop) where
  flow : Key -> Key -> Nat
  row_sum : forall source,
    (∑ target, flow source target) = sourceCapacity source
  column_le : forall target,
    (∑ source, flow source target) <= targetCapacity target
  supported : forall source target,
    ¬ related source target -> flow source target = 0


end
end StatMech.FrontierD
