/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleSymmetry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRectangleBoundary.Part3
import Mathlib.Data.Fin.Rev
open Finset


namespace StatMech.FrontierD

def sixVertexRectangleReflectHorizontal {N M : ℕ}
    (ω : SixVertexRectangleArrows N M) : SixVertexRectangleArrows N M where
  horizontal kj := ω.horizontal (kj.1.rev, kj.2)
  vertical ik := !ω.vertical (ik.1.rev, ik.2)


def sixVertexRectangleReflectVertical {N M : ℕ}
    (ω : SixVertexRectangleArrows N M) : SixVertexRectangleArrows N M where
  horizontal kj := !ω.horizontal (kj.1, kj.2.rev)
  vertical ik := ω.vertical (ik.1, ik.2.rev)

end StatMech.FrontierD
