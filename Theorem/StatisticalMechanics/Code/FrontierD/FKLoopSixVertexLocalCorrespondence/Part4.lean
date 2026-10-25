/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKLoopSixVertexLocalCorrespondence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexSectorTransferBridge.Part2
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Def.StatisticalMechanics.Code.FrontierD.FKLoopSixVertexLocalCorrespondence.Part4
open Finset Matrix


namespace StatMech.FrontierD

@[simp] theorem FKOrientedMedialLoops.toSixVertexConfiguration_seamUpCount
    (loops : FKOrientedMedialLoops T) :
    sixVertexUpCount
        (svTorusVerticalRows T loops.toSixVertexConfiguration.1
          (svFinLast T.height_pos)) =
      loops.seamUpCount := rfl


end StatMech.FrontierD
