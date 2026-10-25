/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKLoopSixVertexLocalCorrespondence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexSectorTransferBridge.Part2
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.FrontierD.FKLoopSixVertexLocalCorrespondence.Part3
open Finset Matrix


namespace StatMech.FrontierD

def FKOrientedMedialLoops.seamUpCount
    (loops : FKOrientedMedialLoops T) : Nat :=
  sixVertexUpCount
    (svTorusVerticalRows T loops.arrows (svFinLast T.height_pos))

end StatMech.FrontierD
