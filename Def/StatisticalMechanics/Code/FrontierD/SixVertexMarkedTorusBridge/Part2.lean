/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedTorusBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexLocalMarkedDisagreementSwitch
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexSectorTransferBridge.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedTorusBridge.Part2
open Finset Matrix Polynomial


namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexTorusMarkedSectorPartitionPolynomial
    (T : EvenTorus) (n : Fin (T.width + 1)) : Real[X] :=
  ∑ omega : SixVertexArrows T,
    if sixVertexUpCount
        (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n.val then
      sixVertexTorusMarkedWeight omega
    else 0

end
end StatMech.FrontierD
