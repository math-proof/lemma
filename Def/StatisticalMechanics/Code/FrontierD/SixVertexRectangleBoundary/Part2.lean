/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertex.Part9
import Instance.StatisticalMechanics.Code.FrontierD.SixVertexRectangleBoundary
open Finset


namespace StatMech.FrontierD

namespace SixVertexRectangleArrows

variable {N M : ℕ}


noncomputable def localWeight (c : ℝ) (ω : SixVertexRectangleArrows N M)
    (v : Fin N × Fin M) : ℝ :=
  if ω.incomingCount v = 2 then if ω.IsCType v then c else 1 else 0


noncomputable def weight (c : ℝ) (ω : SixVertexRectangleArrows N M) : ℝ :=
  ∏ v, ω.localWeight c v

end SixVertexRectangleArrows
end StatMech.FrontierD
