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
import Def.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part20
open scoped BigOperators


namespace StatMech.FrontierA

open SimpleGraph Finset


@[simp] theorem kwOrderedPortAtRank_fst
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (order : KWPortOrder G) (v : V)
    (i : Fin (Fintype.card (KWOutgoingDart (G := G) v))) :
    (kwOrderedPortAtRank order v i).1 = v := rfl

@[simp] theorem kwOrderedPortAtRank_rank
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (order : KWPortOrder G) (v : V)
    (i : Fin (Fintype.card (KWOutgoingDart (G := G) v))) :
    kwOrderedPortRank order (kwOrderedPortAtRank order v i) = i.val := by
  change ((order v) ((order v).symm i)).val = i.val
  rw [Equiv.apply_symm_apply]


end StatMech.FrontierA
