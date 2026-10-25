/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularPortPhase.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAngularPortEmbedding.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRationalNormalization.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAngularPortPhase


namespace StatMech.FrontierA

open SimpleGraph

noncomputable def KWAngularPortRadiusData.rawDartDirection
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {embedding : KWStraightLineEmbedding G}
    (data : KWAngularPortRadiusData embedding)
    (d : (kwOrderedDartPortSplitGraph G
      (kwAngularPortOrder embedding)).Dart) : ℝ :=
  if kwDartOfPort G d.snd = (kwDartOfPort G d.fst).symm then
    (embedding.dartAngle (kwDartOfPort G d.fst)).toReal
  else if kwOrderedPortRank (kwAngularPortOrder embedding) d.fst <
      kwOrderedPortRank (kwAngularPortOrder embedding) d.snd then
    ((embedding.dartAngle (kwDartOfPort G d.fst)).toReal +
      (embedding.dartAngle (kwDartOfPort G d.snd)).toReal) / 2 + Real.pi / 2
  else
    ((embedding.dartAngle (kwDartOfPort G d.fst)).toReal +
      (embedding.dartAngle (kwDartOfPort G d.snd)).toReal) / 2 - Real.pi / 2

end StatMech.FrontierA
