/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoCentralPhysicalBranch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalParticleHole.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall.Part7
import Def.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoCentralPhysicalBranch.Part2


namespace StatMech.FrontierD

noncomputable section

abbrev sixVertexFourByTwoCentralSourceIndex := Fin 28 × Fin 28

abbrev sixVertexFourByTwoCentralTargetIndex :=
  {pair : Fin 50 × Fin 50 // pair.1 ≠ pair.2}

end
end StatMech.FrontierD
