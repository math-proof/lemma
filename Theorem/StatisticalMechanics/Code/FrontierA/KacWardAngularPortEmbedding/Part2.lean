/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularPortEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAngularPortExternal
import Def.StatisticalMechanics.Code.FrontierA.KacWardAngularPortEmbedding


namespace StatMech.FrontierA

open Set SimpleGraph

theorem KWStraightLineEmbedding.exists_angularPortSplitEmbedding
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) :
    Nonempty (KWStraightLineEmbedding
      (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding))) := by
  exact (embedding.exists_angularPortRadiusData.map
    KWAngularPortRadiusData.toStraightLineEmbedding)

end StatMech.FrontierA
