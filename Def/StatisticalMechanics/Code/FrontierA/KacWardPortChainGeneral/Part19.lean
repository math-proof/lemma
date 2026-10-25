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
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part18
open scoped BigOperators


namespace StatMech.FrontierA

open SimpleGraph Finset


def KWOrderedInternalDartFacesPort
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (order : KWPortOrder G) (d : KWOrderedInternalSplitDart G order)
    (q : KWDartPort G) : Prop :=
  d.1.snd.1 = q.1 ∧
    ((kwOrderedPortRank order d.1.fst <
        kwOrderedPortRank order d.1.snd ∧
      kwOrderedPortRank order d.1.snd ≤ kwOrderedPortRank order q) ∨
    (kwOrderedPortRank order d.1.snd <
        kwOrderedPortRank order d.1.fst ∧
      kwOrderedPortRank order q ≤ kwOrderedPortRank order d.1.snd))

end StatMech.FrontierA
