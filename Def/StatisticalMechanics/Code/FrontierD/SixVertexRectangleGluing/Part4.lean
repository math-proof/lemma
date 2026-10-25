/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleGluing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRectangleSymmetry.Part3
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexRectangleGluing
open Finset


namespace StatMech.FrontierD

def sixVertexRectangleReflectedGlue {N M : ℕ}
    {ξ : SixVertexRectangleBoundary N M}
    (omega : SixVertexRectangleFourBoundaryCopies ξ) :
    SixVertexRectangleArrows (N + N) (M + M) :=
  sixVertexRectangleGlueQuadrants omega.1.1
    (sixVertexRectangleReflectHorizontal omega.2.1.1)
    (sixVertexRectangleReflectVertical omega.2.2.1.1)
    (sixVertexRectangleReflectHorizontal
      (sixVertexRectangleReflectVertical omega.2.2.2.1))

end StatMech.FrontierD
