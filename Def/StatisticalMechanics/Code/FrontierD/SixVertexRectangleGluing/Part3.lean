/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleGluing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRectangleSymmetry.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRectangleGluing.Part3
open Finset


namespace StatMech.FrontierD

def sixVertexDoubledToroidalBoundary {N M : ℕ}
    (ξ : SixVertexToroidalBoundary N M) :
    SixVertexToroidalBoundary (N + N) (M + M) :=
  (Fin.addCases ξ.1 (fun j => !ξ.1 j.rev),
    Fin.addCases ξ.2 (fun i => !ξ.2 i.rev))


end StatMech.FrontierD
