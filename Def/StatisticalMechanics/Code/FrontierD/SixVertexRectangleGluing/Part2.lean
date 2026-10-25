/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleGluing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRectangleSymmetry.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRectangleGluing.Part2
open Finset


namespace StatMech.FrontierD

def SixVertexRectangleQuadrantsCompatible {N M : ℕ}
    (lowerLeft lowerRight upperLeft upperRight : SixVertexRectangleArrows N M) : Prop :=
  (sixVertexRectangleBoundary lowerLeft).right =
      (sixVertexRectangleBoundary lowerRight).left ∧
    (sixVertexRectangleBoundary upperLeft).right =
      (sixVertexRectangleBoundary upperRight).left ∧
    (sixVertexRectangleBoundary lowerLeft).top =
      (sixVertexRectangleBoundary upperLeft).bottom ∧
    (sixVertexRectangleBoundary lowerRight).top =
      (sixVertexRectangleBoundary upperRight).bottom


end StatMech.FrontierD
