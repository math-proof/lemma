module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRectangleBoundary.Part3
public import Def.StatisticalMechanics.Code.FrontierD.SixVertexRectangleTorusCut.Part3
open Finset


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleTorusCut.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

@[simp] theorem sixVertexGlue_cut_torus_arrows
    (T : EvenTorus) (ω : SixVertexArrows T) :
    sixVertexGlueTorusArrows T (sixVertexCutTorusArrows T ω) = ω := by
  apply SixVertexArrows.ext <;> funext v <;>
    simp [sixVertexGlueTorusArrows]


end StatMech.FrontierD
