/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexSectorTransferBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBalancedTransferBridge.Part10
open Finset Matrix


namespace StatMech.FrontierD

noncomputable def svTorusSectorArrowPartitionSum
    (T : EvenTorus) (n : Fin (T.width + 1)) (c : Real) : Real :=
  ∑ omega : SixVertexArrows T,
    if sixVertexUpCount
        (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n.val then
      omega.weight c
    else 0

end StatMech.FrontierD
