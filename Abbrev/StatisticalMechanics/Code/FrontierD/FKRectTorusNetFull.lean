/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusNetFull.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusNetMonotonicity
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusConnected.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusNetFull
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

abbrev fkRectFullOpenGraph (R : FKRectTorus) :=
  fkRectOpenGraph R (fkRectConfigurationOfEdges R Finset.univ)

end
end StatMech.FrontierD
