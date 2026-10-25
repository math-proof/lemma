/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairSwitchInterface.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedTorusBridge.Part3
import Instance.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairSwitchInterface
open Finset Matrix Polynomial


namespace StatMech.FrontierD

noncomputable section

abbrev SixVertexMarkedSectorConfiguration
    (T : EvenTorus) (n : Fin (T.width + 1)) :=
  {omega : SixVertexArrows T //
    omega.IceRule /\
      sixVertexUpCount
        (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n.val}


end
end StatMech.FrontierD
