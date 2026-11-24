module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRectangleBoundary.Part3
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRectangleTorusCut.Part3
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

abbrev SixVertexCutRectangles (T : EvenTorus) :=
  Σ ξ : SixVertexToroidalBoundary T.width T.height,
    {ω : SixVertexRectangleArrows T.width T.height //
      sixVertexRectangleBoundary ω = sixVertexToroidalRectangleBoundary ξ}


end StatMech.FrontierD
