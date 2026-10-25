/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertex.Part9
import Def.StatisticalMechanics.Code.FrontierD.SixVertexRectangleBoundary
open Finset


namespace StatMech.FrontierD

namespace SixVertexRectangleArrows

variable {N M : ℕ}


noncomputable instance iceRuleDecidable (ω : SixVertexRectangleArrows N M) :
    Decidable ω.IceRule := Classical.propDecidable _

noncomputable instance isCTypeDecidable (ω : SixVertexRectangleArrows N M)
    (v : Fin N × Fin M) : Decidable (ω.IsCType v) :=
  Classical.propDecidable _


end SixVertexRectangleArrows
end StatMech.FrontierD
