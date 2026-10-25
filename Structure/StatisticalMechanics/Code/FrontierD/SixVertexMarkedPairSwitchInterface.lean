/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairSwitchInterface.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedTorusBridge.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairSwitchInterface.Part2
open Finset Matrix Polynomial


namespace StatMech.FrontierD

noncomputable section

structure SixVertexGlobalMarkedPairSwitch
    (T : EvenTorus)
    (lower middle upper : Fin (T.width + 1)) (k : Nat) where
  toPair :
    SixVertexMarkedSectorConfiguration T lower ×
        SixVertexMarkedSectorConfiguration T upper ->
      SixVertexMarkedSectorConfiguration T middle ×
        SixVertexMarkedSectorConfiguration T middle
  injective : Function.Injective toPair
  mask :
    SixVertexMarkedSectorConfiguration T lower ×
        SixVertexMarkedSectorConfiguration T upper -> SixVertexArrows T
  first_eq : forall pair,
    (toPair pair).1.1 =
      sixVertexTorusSwitchFirst (mask pair) pair.1.1 pair.2.1
  second_eq : forall pair,
    (toPair pair).2.1 =
      sixVertexTorusSwitchSecond (mask pair) pair.1.1 pair.2.1
  local_route_size : forall pair v,
    sixVertexLocalSwitchMaskCount
        (sixVertexTorusLocalSwitchMask (mask pair) v) = 0 \/
      sixVertexLocalSwitchMaskCount
          (sixVertexTorusLocalSwitchMask (mask pair) v) = 2 \/
      sixVertexLocalSwitchMaskCount
          (sixVertexTorusLocalSwitchMask (mask pair) v) = 4
  multiplicity_le : forall pair,
    sixVertexMarkedPairMultiplicity pair.1.1 pair.2.1 k <=
      sixVertexMarkedPairMultiplicity
        (toPair pair).1.1 (toPair pair).2.1 k

end
end StatMech.FrontierD
