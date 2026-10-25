/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleSymmetry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRectangleBoundary.Part3
import Mathlib.Data.Fin.Rev
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRectangleSymmetry
open Finset


namespace StatMech.FrontierD

def sixVertexBoundaryReflectHorizontal {N M : ℕ}
    (ξ : SixVertexRectangleBoundary N M) : SixVertexRectangleBoundary N M where
  left := ξ.right
  right := ξ.left
  bottom i := !ξ.bottom i.rev
  top i := !ξ.top i.rev


def sixVertexBoundaryReflectVertical {N M : ℕ}
    (ξ : SixVertexRectangleBoundary N M) : SixVertexRectangleBoundary N M where
  left j := !ξ.left j.rev
  right j := !ξ.right j.rev
  bottom := ξ.top
  top := ξ.bottom

end StatMech.FrontierD
