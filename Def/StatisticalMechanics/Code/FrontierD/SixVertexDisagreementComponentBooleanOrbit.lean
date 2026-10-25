/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisagreementComponentBooleanOrbit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFullComponentMaskSwap.Part5
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexDisagreementComponentBooleanOrbit
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexDisagreementComponentSetMask
    {T : EvenTorus} (omega eta : SixVertexArrows T)
    (selected : Finset (SixVertexDisagreementComponent omega eta)) :
    SixVertexArrows T := by
  classical
  let graph := sixVertexTorusDisagreementGraph omega eta
  exact
    { horizontal := fun v => decide (∃ component ∈ selected,
        graph.connectedComponentMk (0, v) = component.1)
      vertical := fun v => decide (∃ component ∈ selected,
        graph.connectedComponentMk (1, v) = component.1) }

end
end StatMech.FrontierD
