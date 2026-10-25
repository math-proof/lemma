/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisagreementComponentBooleanOrbit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFullComponentMaskSwap.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDisagreementComponentBooleanOrbit
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

def sixVertexDisagreementComponentCharge
    {T : EvenTorus} (omega eta : SixVertexArrows T)
    (component : SixVertexDisagreementComponent omega eta) : Int :=
  ∑ column : Fin T.width,
    if (sixVertexTorusDisagreementGraph omega eta).connectedComponentMk
          (1, (column, svFinLast T.height_pos)) = component.1 then
      (eta.vertical (column, svFinLast T.height_pos)).toNat -
        (omega.vertical (column, svFinLast T.height_pos)).toNat
    else 0


end
end StatMech.FrontierD
