/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularSplitSpinor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardArbitraryValenceReduction
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPrincipalAngleMultiaffine
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAngularSplitSpinor


namespace StatMech.FrontierA

open SimpleGraph

open scoped BigOperators


noncomputable def kwAngularSplitSpinorDirection
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (d : (kwOrderedDartPortSplitGraph G
      (kwAngularPortOrder embedding)).Dart) : Complex :=
  if kwDartOfPort G d.snd = (kwDartOfPort G d.fst).symm then
    (kwPortAngleRoot embedding d.fst) ^ 2
  else if kwOrderedPortRank (kwAngularPortOrder embedding) d.fst <
      kwOrderedPortRank (kwAngularPortOrder embedding) d.snd then
    -1
  else 1

end StatMech.FrontierA
