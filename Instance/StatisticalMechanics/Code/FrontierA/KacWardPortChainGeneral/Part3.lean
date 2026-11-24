module
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAcyclicElimination.Part3
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardStraightLineEmbedding.Part2
public import Mathlib.Data.Finset.Sort
public import Def.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part6
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open SimpleGraph Finset


noncomputable instance kwOrderedDartPortSplitGraph_decidableAdj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (order : KWPortOrder G) :
    DecidableRel (kwOrderedDartPortSplitGraph G order).Adj :=
  Classical.decRel _

noncomputable instance kwOrderedDartPortSplitGraph_dart_decidableEq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G) :
    DecidableEq (kwOrderedDartPortSplitGraph G order).Dart :=
  Classical.decEq _

end StatMech.FrontierA
