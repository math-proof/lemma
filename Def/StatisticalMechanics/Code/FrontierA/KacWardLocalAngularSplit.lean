/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardLocalAngularSplit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part32
import Structure.StatisticalMechanics.Code.FrontierA.KacWardLocalAngularSplit
open scoped BigOperators


namespace StatMech.FrontierA

open SimpleGraph Finset


noncomputable def kwLocalAngularSplitPhase
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G)
    (d e : (kwOrderedDartPortSplitGraph G
      (data.order)).Dart) : ℂ :=
  if _hd : kwDartOfPort G d.snd = (kwDartOfPort G d.fst).symm then
    if _he : kwDartOfPort G e.snd = (kwDartOfPort G e.fst).symm then 1
    else if kwOrderedPortRank (data.order) e.fst <
        kwOrderedPortRank (data.order) e.snd then
      -Complex.I * (data.root e.fst)⁻¹
    else
      Complex.I * (data.root e.fst)⁻¹
  else if _he : kwDartOfPort G e.snd =
      (kwDartOfPort G e.fst).symm then
    data.root e.fst
  else 1

end StatMech.FrontierA
