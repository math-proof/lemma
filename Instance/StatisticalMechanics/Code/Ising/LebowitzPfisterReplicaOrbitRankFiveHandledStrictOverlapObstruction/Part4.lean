/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictOverlapObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveHandledStrictInvariant.Part8
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveHandledStrictOverlapObstruction.Part7


namespace StatMech.Ising.LPRankFiveDoubledRectangleOverlapObstruction

instance relatedDecidable (z : StrictSource) (y : Target) :
    Decidable (Related z y) := by
  unfold Related
  infer_instance

end StatMech.Ising.LPRankFiveDoubledRectangleOverlapObstruction
