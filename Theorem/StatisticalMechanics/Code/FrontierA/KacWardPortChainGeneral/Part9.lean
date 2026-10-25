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
import Def.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part9
open scoped BigOperators


namespace StatMech.FrontierA

open SimpleGraph Finset


@[simp] theorem kwOrderedSplitDartBlockEquiv_inl
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (d : G.Dart) :
    kwOrderedSplitDartBlockEquiv G order (Sum.inl d) =
      (kwOrderedExternalSplitDartOfDart G order d).1 := by
  rfl

@[simp] theorem kwOrderedSplitDartBlockEquiv_inr
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (d : KWOrderedInternalSplitDart G order) :
    kwOrderedSplitDartBlockEquiv G order (Sum.inr d) = d.1 := by
  rfl


end StatMech.FrontierA
