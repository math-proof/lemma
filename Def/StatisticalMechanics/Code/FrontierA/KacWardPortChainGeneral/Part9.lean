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
import Instance.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part4
open scoped BigOperators


namespace StatMech.FrontierA

open SimpleGraph Finset


noncomputable def kwOrderedSplitDartPartitionEquiv
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G) :
    KWOrderedExternalSplitDart G order ⊕
        KWOrderedInternalSplitDart G order ≃
      (kwOrderedDartPortSplitGraph G order).Dart := by
  classical
  exact Equiv.sumCompl (fun delta :
      (kwOrderedDartPortSplitGraph G order).Dart ↦
    kwDartOfPort G delta.snd = (kwDartOfPort G delta.fst).symm)


noncomputable def kwOrderedSplitDartBlockEquiv
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G) :
    G.Dart ⊕ KWOrderedInternalSplitDart G order ≃
      (kwOrderedDartPortSplitGraph G order).Dart :=
  (Equiv.sumCongr (kwOrderedExternalSplitDartEquiv G order) (Equiv.refl _)).trans
    (kwOrderedSplitDartPartitionEquiv G order)

end StatMech.FrontierA
