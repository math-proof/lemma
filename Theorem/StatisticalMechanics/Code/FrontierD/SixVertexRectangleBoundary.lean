/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertex.Part9
import Def.StatisticalMechanics.Code.FrontierD.SixVertexRectangleBoundary.Part2
open Finset


namespace StatMech.FrontierD

namespace SixVertexRectangleArrows

variable {N M : ℕ}


theorem localWeight_nonneg {c : ℝ} (hc : 0 ≤ c)
    (ω : SixVertexRectangleArrows N M) (v : Fin N × Fin M) :
    0 ≤ ω.localWeight c v := by
  unfold localWeight
  split_ifs <;> positivity

theorem weight_nonneg {c : ℝ} (hc : 0 ≤ c)
    (ω : SixVertexRectangleArrows N M) : 0 ≤ ω.weight c := by
  exact Finset.prod_nonneg fun v _ => localWeight_nonneg hc ω v

end SixVertexRectangleArrows
end StatMech.FrontierD
