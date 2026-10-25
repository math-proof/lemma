/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexSectorTransferBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBalancedTransferBridge.Part10
import Def.StatisticalMechanics.Code.FrontierD.SixVertexSectorTransferBridge.Part2
open Finset Matrix


namespace StatMech.FrontierD

theorem sixVertexTorusFixedChargePartitionSum_eq_sectorTrace
    (T : EvenTorus) (r : Nat) (hr : r <= T.width / 2) (c : Real) :
    sixVertexTorusFixedChargePartitionSum T r hr c =
      Matrix.trace
        (sixVertexSectorTransfer T.width (T.width / 2 - r) c ^ T.height) := by
  exact svTorusSectorArrowPartitionSum_eq_sectorTrace T _ c

end StatMech.FrontierD
