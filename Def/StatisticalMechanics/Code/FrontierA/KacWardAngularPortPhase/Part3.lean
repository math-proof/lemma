/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularPortPhase.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAngularPortEmbedding.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRationalNormalization.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAngularPortPhase.Part3


namespace StatMech.FrontierA

open SimpleGraph

noncomputable def KWAngularPortRadiusData.phaseGauge
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {embedding : KWStraightLineEmbedding G}
    (data : KWAngularPortRadiusData embedding)
    (d : (kwOrderedDartPortSplitGraph G
      (kwAngularPortOrder embedding)).Dart) : ℂ :=
  if kwDartOfPort G d.snd = (kwDartOfPort G d.fst).symm then 1
  else kwRawDirectionRoot (data.rawDartDirection d)

end StatMech.FrontierA
