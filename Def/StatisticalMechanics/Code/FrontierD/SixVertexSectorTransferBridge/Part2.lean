/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexSectorTransferBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBalancedTransferBridge.Part10
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexSectorTransferBridge
open Finset Matrix


namespace StatMech.FrontierD

noncomputable def sixVertexTorusFixedChargePartitionSum
    (T : EvenTorus) (r : Nat) (_hr : r <= T.width / 2) (c : Real) : Real :=
  svTorusSectorArrowPartitionSum T
    ⟨T.width / 2 - r, Nat.lt_succ_of_le
      ((Nat.sub_le _ _).trans (Nat.div_le_self T.width 2))⟩ c

end StatMech.FrontierD
