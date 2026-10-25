/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleTorusCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRectangleBoundary.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRectangleTorusCut.Part2
open Finset


namespace StatMech.FrontierD

def sixVertexGlueTorusArrows (T : EvenTorus)
    (ω : SixVertexRectangleArrows T.width T.height) : SixVertexArrows T where
  horizontal ij := ω.horizontal (ij.1.succ, ij.2)
  vertical ij := ω.vertical (ij.1, ij.2.succ)

end StatMech.FrontierD
