/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertex.Part9
import Structure.StatisticalMechanics.Code.FrontierD.SixVertexRectangleBoundary
open Finset


namespace StatMech.FrontierD

namespace SixVertexRectangleArrows

variable {N M : ℕ}


def incomingCount (ω : SixVertexRectangleArrows N M) (v : Fin N × Fin M) : ℕ :=
  (ω.horizontal (v.1.castSucc, v.2)).toNat +
    (!ω.horizontal (v.1.succ, v.2)).toNat +
    (ω.vertical (v.1, v.2.castSucc)).toNat +
    (!ω.vertical (v.1, v.2.succ)).toNat


def IceRule (ω : SixVertexRectangleArrows N M) : Prop :=
  ∀ v, ω.incomingCount v = 2


def IsCType (ω : SixVertexRectangleArrows N M) (v : Fin N × Fin M) : Prop :=
  ((ω.horizontal (v.1.castSucc, v.2)).toNat +
      (!ω.horizontal (v.1.succ, v.2)).toNat = 0) ∨
    ((ω.horizontal (v.1.castSucc, v.2)).toNat +
      (!ω.horizontal (v.1.succ, v.2)).toNat = 2)

end SixVertexRectangleArrows
end StatMech.FrontierD
