/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleTorusCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRectangleBoundary.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexRectangleTorusCut.Part2
open Finset


namespace StatMech.FrontierD

@[simp] theorem sixVertexCutTorusArrows_horizontal_zero
    (T : EvenTorus) (ω : SixVertexArrows T) (j : Fin T.height) :
    (sixVertexCutTorusArrows T ω).horizontal (0, j) =
      ω.horizontal (finLastOfPos T.width_pos, j) := by
  simp [sixVertexCutTorusArrows]

@[simp] theorem sixVertexCutTorusArrows_horizontal_succ
    (T : EvenTorus) (ω : SixVertexArrows T) (i : Fin T.width)
    (j : Fin T.height) :
    (sixVertexCutTorusArrows T ω).horizontal (i.succ, j) =
      ω.horizontal (i, j) := by
  simp [sixVertexCutTorusArrows]

@[simp] theorem sixVertexCutTorusArrows_horizontal_last
    (T : EvenTorus) (ω : SixVertexArrows T) (j : Fin T.height) :
    (sixVertexCutTorusArrows T ω).horizontal (Fin.last T.width, j) =
      ω.horizontal (finLastOfPos T.width_pos, j) := by
  simpa only [finLastOfPos_succ] using
    sixVertexCutTorusArrows_horizontal_succ T ω
      (finLastOfPos T.width_pos) j

@[simp] theorem sixVertexCutTorusArrows_vertical_zero
    (T : EvenTorus) (ω : SixVertexArrows T) (i : Fin T.width) :
    (sixVertexCutTorusArrows T ω).vertical (i, 0) =
      ω.vertical (i, finLastOfPos T.height_pos) := by
  simp [sixVertexCutTorusArrows]

@[simp] theorem sixVertexCutTorusArrows_vertical_succ
    (T : EvenTorus) (ω : SixVertexArrows T) (i : Fin T.width)
    (j : Fin T.height) :
    (sixVertexCutTorusArrows T ω).vertical (i, j.succ) =
      ω.vertical (i, j) := by
  simp [sixVertexCutTorusArrows]

@[simp] theorem sixVertexCutTorusArrows_vertical_last
    (T : EvenTorus) (ω : SixVertexArrows T) (i : Fin T.width) :
    (sixVertexCutTorusArrows T ω).vertical (i, Fin.last T.height) =
      ω.vertical (i, finLastOfPos T.height_pos) := by
  simpa only [finLastOfPos_succ] using
    sixVertexCutTorusArrows_vertical_succ T ω i
      (finLastOfPos T.height_pos)

theorem sixVertexCutTorusArrows_boundary
    (T : EvenTorus) (ω : SixVertexArrows T) :
    sixVertexRectangleBoundary (sixVertexCutTorusArrows T ω) =
      sixVertexToroidalRectangleBoundary (sixVertexTorusSeam T ω) := by
  apply SixVertexRectangleBoundary.ext
  · funext j
    simp [sixVertexRectangleBoundary, sixVertexToroidalRectangleBoundary,
      sixVertexTorusSeam]
  · funext j
    simp [sixVertexRectangleBoundary, sixVertexToroidalRectangleBoundary,
      sixVertexTorusSeam]
  · funext i
    simp [sixVertexRectangleBoundary, sixVertexToroidalRectangleBoundary,
      sixVertexTorusSeam]
  · funext i
    simp [sixVertexRectangleBoundary, sixVertexToroidalRectangleBoundary,
      sixVertexTorusSeam]


end StatMech.FrontierD
