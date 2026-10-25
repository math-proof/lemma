/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisagreementComponentBooleanOrbit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFullComponentMaskSwap.Part5
import Instance.StatisticalMechanics.Code.FrontierD.SixVertexDisagreementComponentBooleanOrbit
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

abbrev SixVertexDisagreementComponent
    {T : EvenTorus} (omega eta : SixVertexArrows T) :=
  {component :
      (sixVertexTorusDisagreementGraph omega eta).ConnectedComponent //
    ∃ edge : SixVertexTorusEdge T,
      sixVertexTorusEdgeDisagrees omega eta edge ∧
        (sixVertexTorusDisagreementGraph omega eta).connectedComponentMk edge =
          component}


end
end StatMech.FrontierD
