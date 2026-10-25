/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertex.Part9
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexRectangleBoundary
open Finset


namespace StatMech.FrontierD

def sixVertexToroidalRectangleBoundary {N M : ℕ}
    (ξ : SixVertexToroidalBoundary N M) : SixVertexRectangleBoundary N M where
  left := ξ.1
  right := ξ.1
  bottom := ξ.2
  top := ξ.2


def SixVertexToroidalBoundary.Balanced {N M : ℕ}
    (ξ : SixVertexToroidalBoundary N M) : Prop :=
  #{i | ξ.2 i} = N / 2

end StatMech.FrontierD
