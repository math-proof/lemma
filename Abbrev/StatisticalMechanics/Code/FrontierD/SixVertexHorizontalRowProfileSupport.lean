/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalRowProfileSupport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.EqualFiberHall
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalResidualCompletions.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileLayerSymmetry.Part5
import Def.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalRowProfileSupport
open Finset


namespace StatMech.FrontierD

noncomputable section

abbrev SixVertexHorizontalRowZeroProfile (T : EvenTorus) :=
  Fin T.height -> Nat

end
end StatMech.FrontierD
