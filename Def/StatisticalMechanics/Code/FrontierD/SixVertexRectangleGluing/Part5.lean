/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleGluing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRectangleSymmetry.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRectangleGluing.Part5
open Finset


namespace StatMech.FrontierD

def sixVertexRectangleReflectedGlueBoundaryFiber {N M : ℕ}
    (hN : 0 < N) (hM : 0 < M)
    (ξ : SixVertexToroidalBoundary N M) :
    SixVertexRectangleFourBoundaryCopies
        (sixVertexToroidalRectangleBoundary ξ) →
      SixVertexRectangleBoundaryFiber
        (sixVertexToroidalRectangleBoundary
          (sixVertexDoubledToroidalBoundary ξ)) :=
  fun omega => ⟨sixVertexRectangleReflectedGlue omega,
    sixVertexRectangleReflectedGlue_boundary hN hM omega⟩

end StatMech.FrontierD
