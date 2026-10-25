/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLocalDisagreementSwitch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKLoopSixVertexLocalCorrespondence.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRectangleTorusCut.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexLocalDisagreementSwitch.Part5
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

def sixVertexTorusSwitchFirst
    (mask omega eta : SixVertexArrows T) : SixVertexArrows T where
  horizontal e := if mask.horizontal e then eta.horizontal e
    else omega.horizontal e
  vertical e := if mask.vertical e then eta.vertical e
    else omega.vertical e


def sixVertexTorusSwitchSecond
    (mask omega eta : SixVertexArrows T) : SixVertexArrows T where
  horizontal e := if mask.horizontal e then omega.horizontal e
    else eta.horizontal e
  vertical e := if mask.vertical e then omega.vertical e
    else eta.vertical e


def sixVertexTorusLocalSwitchMask
    (mask : SixVertexArrows T) (v : T.Vertex) :
    SixVertexLocalIncomingPattern :=
  ![mask.horizontal (SixVertexArrows.cyclicPred T.width_pos v.1, v.2),
    mask.horizontal v,
    mask.vertical (v.1, SixVertexArrows.cyclicPred T.height_pos v.2),
    mask.vertical v]

end
end StatMech.FrontierD
