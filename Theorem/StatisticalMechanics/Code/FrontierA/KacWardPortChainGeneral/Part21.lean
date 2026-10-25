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
import Def.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part21
open scoped BigOperators


namespace StatMech.FrontierA

open SimpleGraph Finset


@[simp] theorem kwOrderedIncreasingInternalDartFrom_fst
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (p : KWDartPort G)
    (h : kwOrderedPortRank order p + 1 <
      Fintype.card (KWOutgoingDart (G := G) p.1)) :
    (kwOrderedIncreasingInternalDartFrom G order p h).1.fst = p := by
  change ((kwOrderedInternalSplitDartEquiv G order).symm
    ⟨(p, kwOrderedPortAtRank order p.1
      ⟨kwOrderedPortRank order p + 1, h⟩), _⟩).1.fst = p
  rfl

@[simp] theorem kwOrderedIncreasingInternalDartFrom_rank_snd
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (p : KWDartPort G)
    (h : kwOrderedPortRank order p + 1 <
      Fintype.card (KWOutgoingDart (G := G) p.1)) :
    kwOrderedPortRank order
        (kwOrderedIncreasingInternalDartFrom G order p h).1.snd =
      kwOrderedPortRank order p + 1 := by
  change kwOrderedPortRank order (kwOrderedPortAtRank order p.1
    ⟨kwOrderedPortRank order p + 1, h⟩) = _
  simp


end StatMech.FrontierA
