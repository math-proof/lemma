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
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part10
open scoped BigOperators


namespace StatMech.FrontierA

open SimpleGraph Finset


def kwOrderedPortInternalGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G) :
    SimpleGraph (KWDartPort G) where
  Adj p q := p.1 = q.1 ∧
    (kwOrderedPortRank order p + 1 = kwOrderedPortRank order q ∨
      kwOrderedPortRank order q + 1 = kwOrderedPortRank order p)
  symm := by
    constructor
    rintro p q ⟨hfst, hrank⟩
    exact ⟨hfst.symm, hrank.symm⟩
  loopless := ⟨by
    rintro p ⟨-, hrank⟩
    omega⟩

end StatMech.FrontierA
