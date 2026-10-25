/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleGluing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRectangleSymmetry.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRectangleGluing.Part4
open Finset


namespace StatMech.FrontierD

abbrev SixVertexRectangleBoundaryFiber {N M : ℕ}
    (ξ : SixVertexRectangleBoundary N M) :=
  {omega : SixVertexRectangleArrows N M // sixVertexRectangleBoundary omega = ξ}


abbrev SixVertexRectangleFourBoundaryCopies {N M : ℕ}
    (ξ : SixVertexRectangleBoundary N M) :=
  SixVertexRectangleBoundaryFiber ξ ×
    SixVertexRectangleBoundaryFiber ξ ×
    SixVertexRectangleBoundaryFiber ξ ×
    SixVertexRectangleBoundaryFiber ξ


end StatMech.FrontierD
