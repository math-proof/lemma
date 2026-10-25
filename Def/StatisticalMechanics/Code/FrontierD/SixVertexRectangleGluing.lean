/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleGluing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRectangleSymmetry.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRectangleGluing
open Finset


namespace StatMech.FrontierD

def sixVertexRectangleGlueQuadrants {N M : ℕ}
    (lowerLeft lowerRight upperLeft upperRight : SixVertexRectangleArrows N M) :
    SixVertexRectangleArrows (N + N) (M + M) where
  horizontal xy :=
    Fin.addCases (m := N) (n := N + 1)
      (fun xLeft =>
        Fin.addCases (m := M) (n := M)
          (fun yBottom => lowerLeft.horizontal (xLeft.castSucc, yBottom))
          (fun yTop => upperLeft.horizontal (xLeft.castSucc, yTop)) xy.2)
      (fun xRight =>
        Fin.addCases (m := M) (n := M)
          (fun yBottom => lowerRight.horizontal (xRight, yBottom))
          (fun yTop => upperRight.horizontal (xRight, yTop)) xy.2) xy.1
  vertical xy :=
    Fin.addCases (m := N) (n := N)
      (fun xLeft =>
        Fin.addCases (m := M) (n := M + 1)
          (fun yBottom => lowerLeft.vertical (xLeft, yBottom.castSucc))
          (fun yTop => upperLeft.vertical (xLeft, yTop)) xy.2)
      (fun xRight =>
        Fin.addCases (m := M) (n := M + 1)
          (fun yBottom => lowerRight.vertical (xRight, yBottom.castSucc))
          (fun yTop => upperRight.vertical (xRight, yTop)) xy.2) xy.1


def sixVertexRectangleGlueBoundary {N M : ℕ}
    (lowerLeft lowerRight upperLeft upperRight : SixVertexRectangleBoundary N M) :
    SixVertexRectangleBoundary (N + N) (M + M) where
  left := Fin.addCases lowerLeft.left upperLeft.left
  right := Fin.addCases lowerRight.right upperRight.right
  bottom := Fin.addCases lowerLeft.bottom lowerRight.bottom
  top := Fin.addCases upperLeft.top upperRight.top

end StatMech.FrontierD
