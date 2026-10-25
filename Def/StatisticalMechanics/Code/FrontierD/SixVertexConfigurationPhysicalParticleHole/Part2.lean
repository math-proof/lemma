/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPhysicalParticleHole.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalPairedBranch.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalParticleHole
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexPhysicalParticleHoleMiddle
    {T : EvenTorus} (middle : Fin (T.width + 1)) : Fin (T.width + 1) :=
  ⟨T.width - middle.val, by omega⟩

end
end StatMech.FrontierD
