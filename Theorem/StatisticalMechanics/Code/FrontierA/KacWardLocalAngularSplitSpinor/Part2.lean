/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardLocalAngularSplitSpinor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardLocalAngularSplit.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAngularSplitSpinor.Part3
import Def.StatisticalMechanics.Code.FrontierA.KacWardLocalAngularSplitSpinor


namespace StatMech.FrontierA

open SimpleGraph

open scoped BigOperators


theorem kwLocalAngularSplitSpinorGauge_ne_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G)
    (d : (kwOrderedDartPortSplitGraph G
      (data.order)).Dart) :
    kwLocalAngularSplitSpinorGauge data d ≠ 0 := by
  classical
  unfold kwLocalAngularSplitSpinorGauge
  by_cases hmatching :
      kwDartOfPort G d.snd = (kwDartOfPort G d.fst).symm
  · simp [hmatching]
  · by_cases hincreasing :
        kwOrderedPortRank (data.order) d.fst <
          kwOrderedPortRank (data.order) d.snd
    · simp [hmatching, hincreasing]
    · simp [hmatching, hincreasing]


end StatMech.FrontierA
