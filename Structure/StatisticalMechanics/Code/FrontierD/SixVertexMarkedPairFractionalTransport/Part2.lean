/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairFractionalTransport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairSwitchInterface.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairFractionalTransport
open Finset Matrix Polynomial


namespace StatMech.FrontierD

noncomputable section

structure FiniteFractionalTransportOn
    (Source Target : Type*) [Fintype Source] [Fintype Target]
    (sourceMass : Source -> Real) (targetCapacity : Target -> Real)
    (related : Source -> Target -> Prop)
    extends FiniteFractionalTransport
      Source Target sourceMass targetCapacity where
  supported : forall source target,
    ¬ related source target -> flow source target = 0

end
end StatMech.FrontierD
