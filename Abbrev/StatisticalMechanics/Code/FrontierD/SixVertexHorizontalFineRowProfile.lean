/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalFineRowProfile.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalRowProfileAggregate.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalFineRowProfile
open Finset


namespace StatMech.FrontierD

noncomputable section

abbrev SixVertexHorizontalBoundedFineRowProfile (T : EvenTorus) :=
  Fin T.height -> Fin (2 * T.width + 1) × Fin (2 * T.width + 1)

end
end StatMech.FrontierD
