/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLocalDisagreementSwitch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKLoopSixVertexLocalCorrespondence.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRectangleTorusCut.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexLocalDisagreementSwitch.Part3
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

def sixVertexRectangleLocalIncomingPattern
    (omega : SixVertexRectangleArrows N M) (v : Fin N × Fin M) :
    SixVertexLocalIncomingPattern :=
  ![omega.horizontal (v.1.castSucc, v.2),
    !omega.horizontal (v.1.succ, v.2),
    omega.vertical (v.1, v.2.castSucc),
    !omega.vertical (v.1, v.2.succ)]

end
end StatMech.FrontierD
