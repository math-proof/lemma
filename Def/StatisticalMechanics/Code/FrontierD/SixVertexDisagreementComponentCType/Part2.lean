/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisagreementComponentCType.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDisagreementDecomposition.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairDecoratedHall.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDisagreementComponentCType.Part2
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexFullDisagreementMask
    {T : EvenTorus} (omega eta : SixVertexArrows T) : SixVertexArrows T where
  horizontal v := decide (omega.horizontal v ≠ eta.horizontal v)
  vertical v := decide (omega.vertical v ≠ eta.vertical v)


end
end StatMech.FrontierD
