/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKLoopSixVertexLocalCorrespondence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexSectorTransferBridge.Part2
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.FrontierD.FKLoopSixVertexLocalCorrespondence.Part4
open Finset Matrix


namespace StatMech.FrontierD

noncomputable def fkOrientedLoopSectorPartitionSum
    (T : EvenTorus) (n : Fin (T.width + 1)) (lam : Real) : Real :=
  ∑ omega : SixVertexArrows T,
    if sixVertexUpCount
        (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n.val then
      ∑ pairing : FKMedialLoopPairing T,
        fkOrientedLoopPairingWeight lam pairing omega
    else 0


end StatMech.FrontierD
