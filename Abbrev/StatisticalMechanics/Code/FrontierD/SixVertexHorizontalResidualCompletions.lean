/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalResidualCompletions.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalActualDeficitSupport.Part3
import Instance.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalResidualCompletions


namespace StatMech.FrontierD

noncomputable section

abbrev SixVertexHorizontalPairSectorCompletions
    (T : EvenTorus) (left right : Fin (T.width + 1))
    (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T) :=
  SixVertexHorizontalSectorCompletion T left horizontal.1 ×
    SixVertexHorizontalSectorCompletion T right horizontal.2

end
end StatMech.FrontierD
