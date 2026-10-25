/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularSplitSpinor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardArbitraryValenceReduction
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPrincipalAngleMultiaffine
import Def.StatisticalMechanics.Code.FrontierA.KacWardAngularSplitSpinor


namespace StatMech.FrontierA

open SimpleGraph

open scoped BigOperators


theorem kwAngularSplitSpinorGauge_ne_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (d : (kwOrderedDartPortSplitGraph G
      (kwAngularPortOrder embedding)).Dart) :
    kwAngularSplitSpinorGauge embedding d ≠ 0 := by
  classical
  unfold kwAngularSplitSpinorGauge
  by_cases hmatching :
      kwDartOfPort G d.snd = (kwDartOfPort G d.fst).symm
  · simp [hmatching]
  · by_cases hincreasing :
        kwOrderedPortRank (kwAngularPortOrder embedding) d.fst <
          kwOrderedPortRank (kwAngularPortOrder embedding) d.snd
    · simp [hmatching, hincreasing]
    · simp [hmatching, hincreasing]


end StatMech.FrontierA
