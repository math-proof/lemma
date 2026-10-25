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
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part21
open scoped BigOperators


namespace StatMech.FrontierA

open SimpleGraph Finset


noncomputable def kwOrderedDecreasingInternalDartFrom
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (p : KWDartPort G) (h : 0 < kwOrderedPortRank order p) :
    KWOrderedInternalSplitDart G order :=
  (kwOrderedInternalSplitDartEquiv G order).symm ⟨
    (p, kwOrderedPortAtRank order p.1
      ⟨kwOrderedPortRank order p - 1, by
        exact lt_of_le_of_lt (Nat.sub_le _ _) (order p.1 p.2).isLt⟩), by
      exact ⟨rfl, Or.inr (by simp; omega)⟩⟩

end StatMech.FrontierA
