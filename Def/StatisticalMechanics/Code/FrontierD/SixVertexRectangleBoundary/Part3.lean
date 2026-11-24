module
public import Def.StatisticalMechanics.Code.FrontierD.SixVertex.Part9
public import Structure.StatisticalMechanics.Code.FrontierD.SixVertexRectangleBoundary.Part2
open Finset


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleBoundary.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

def sixVertexRectangleBoundary {N M : ℕ} (ω : SixVertexRectangleArrows N M) :
    SixVertexRectangleBoundary N M where
  left j := ω.horizontal (0, j)
  right j := ω.horizontal (Fin.last N, j)
  bottom i := ω.vertical (i, 0)
  top i := ω.vertical (i, Fin.last M)


end StatMech.FrontierD
