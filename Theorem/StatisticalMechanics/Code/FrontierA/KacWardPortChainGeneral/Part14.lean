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
import Def.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part14
open scoped BigOperators


namespace StatMech.FrontierA

open SimpleGraph Finset


@[simp] theorem kwOrderedInternalSplitDartEquiv_toProd
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (delta : KWOrderedInternalSplitDart G order) :
    (kwOrderedInternalSplitDartEquiv G order delta).toProd =
      delta.1.toProd := by
  rfl

@[simp] theorem kwOrderedInternalSplitDartEquiv_symm_toProd
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (delta : (kwOrderedPortInternalGraph G order).Dart) :
    ((kwOrderedInternalSplitDartEquiv G order).symm delta).1.toProd =
      delta.toProd := by
  rfl


end StatMech.FrontierA
