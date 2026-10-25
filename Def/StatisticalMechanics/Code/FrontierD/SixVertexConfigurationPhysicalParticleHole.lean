/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPhysicalParticleHole.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalPairedBranch.Part2
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexArrowsComplement {T : EvenTorus}
    (omega : SixVertexArrows T) : SixVertexArrows T where
  horizontal v := !omega.horizontal v
  vertical v := !omega.vertical v

end
end StatMech.FrontierD
