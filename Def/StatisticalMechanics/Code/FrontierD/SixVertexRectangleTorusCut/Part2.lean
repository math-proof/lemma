/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleTorusCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRectangleBoundary.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRectangleTorusCut
open Finset


namespace StatMech.FrontierD

def sixVertexTorusSeam (T : EvenTorus) (ω : SixVertexArrows T) :
    SixVertexToroidalBoundary T.width T.height :=
  (fun j => ω.horizontal (finLastOfPos T.width_pos, j),
    fun i => ω.vertical (i, finLastOfPos T.height_pos))


def sixVertexCutTorusArrows (T : EvenTorus) (ω : SixVertexArrows T) :
    SixVertexRectangleArrows T.width T.height where
  horizontal kj := Fin.cases
    (ω.horizontal (finLastOfPos T.width_pos, kj.2))
    (fun i => ω.horizontal (i, kj.2)) kj.1
  vertical ik := Fin.cases
    (ω.vertical (ik.1, finLastOfPos T.height_pos))
    (fun j => ω.vertical (ik.1, j)) ik.2

end StatMech.FrontierD
