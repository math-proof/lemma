/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisagreementComponentCType.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDisagreementDecomposition.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairDecoratedHall.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDisagreementComponentCType
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexTorusMaskSeamTransfer
    {T : EvenTorus} (mask omega eta : SixVertexArrows T) : Int :=
  ∑ i : Fin T.width,
    if mask.vertical (i, svFinLast T.height_pos) then
      (eta.vertical (i, svFinLast T.height_pos)).toNat -
        (omega.vertical (i, svFinLast T.height_pos)).toNat
    else 0

end
end StatMech.FrontierD
