/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairFractionalTransport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairSwitchInterface.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairFractionalTransport.Part2
open Finset Matrix Polynomial


namespace StatMech.FrontierD

noncomputable section

abbrev SixVertexMarkedPairSource
    (T : EvenTorus) (lower upper : Fin (T.width + 1)) :=
  SixVertexMarkedSectorConfiguration T lower ×
    SixVertexMarkedSectorConfiguration T upper


abbrev SixVertexMarkedPairTarget
    (T : EvenTorus) (middle : Fin (T.width + 1)) :=
  SixVertexMarkedSectorConfiguration T middle ×
    SixVertexMarkedSectorConfiguration T middle


end
end StatMech.FrontierD
