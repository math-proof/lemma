/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFullComponentMaskSwap.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexLoopLexUnitFineRelation
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFullComponentMaskSwap
open Finset


namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexSeedDisagreementComponentMask
    {T : EvenTorus} (omega eta : SixVertexArrows T)
    (seed : SixVertexTorusEdge T) : SixVertexArrows T := by
  classical
  let G := sixVertexTorusDisagreementGraph omega eta
  exact
    { horizontal := fun v => decide (G.Reachable seed (0, v))
      vertical := fun v => decide (G.Reachable seed (1, v)) }

end
end StatMech.FrontierD
