/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAcyclicElimination.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardStraightLineEmbedding.Part2
import Mathlib.Data.Finset.Sort
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part16
open scoped BigOperators


namespace StatMech.FrontierA

open SimpleGraph Finset


noncomputable def kwAngularSplitPhase
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (d e : (kwOrderedDartPortSplitGraph G
      (kwAngularPortOrder embedding)).Dart) : ℂ :=
  if _hd : kwDartOfPort G d.snd = (kwDartOfPort G d.fst).symm then
    if _he : kwDartOfPort G e.snd = (kwDartOfPort G e.fst).symm then 1
    else if kwOrderedPortRank (kwAngularPortOrder embedding) e.fst <
        kwOrderedPortRank (kwAngularPortOrder embedding) e.snd then
      -Complex.I * (kwPortAngleRoot embedding e.fst)⁻¹
    else
      Complex.I * (kwPortAngleRoot embedding e.fst)⁻¹
  else if _he : kwDartOfPort G e.snd =
      (kwDartOfPort G e.fst).symm then
    kwPortAngleRoot embedding e.fst
  else 1

end StatMech.FrontierA
