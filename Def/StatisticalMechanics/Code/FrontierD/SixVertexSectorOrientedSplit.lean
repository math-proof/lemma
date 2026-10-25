/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexSectorOrientedSplit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexCoordinateBethe.Part6
import Instance.StatisticalMechanics.Code.FrontierD.SixVertexSectorOrientedSplit
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexSectorForwardTransfer
    (N n : Nat) (c : Real) :
    Matrix (SixVertexSector N n) (SixVertexSector N n) Real := by
  classical
  exact fun x y =>
    if SixVertexForwardInterlaced
        (sixVertexSectorRow x) (sixVertexSectorRow y) then
      c ^ sixVertexRowDistance
        (sixVertexSectorRow x) (sixVertexSectorRow y)
    else 0

end
end StatMech.FrontierD
