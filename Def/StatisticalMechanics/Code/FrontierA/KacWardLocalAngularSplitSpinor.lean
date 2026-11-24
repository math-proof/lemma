module
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardLocalAngularSplit.Part3
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAngularSplitSpinor.Part3
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardLocalAngularSplitSpinor


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardLocalAngularSplitSpinor.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open SimpleGraph

open scoped BigOperators


noncomputable def kwLocalAngularSplitSpinorGauge
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G)
    (d : (kwOrderedDartPortSplitGraph G
      (data.order)).Dart) : Complex :=
  if kwDartOfPort G d.snd = (kwDartOfPort G d.fst).symm then 1
  else if kwOrderedPortRank (data.order) d.fst <
      kwOrderedPortRank (data.order) d.snd then
    Complex.I
  else 1

end StatMech.FrontierA
