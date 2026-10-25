/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularSplitUnitCycleReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAngularSplitCycleReversal


namespace StatMech.FrontierA

open SimpleGraph


def KWAngularSplitCyclePhaseSign
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) : Prop :=
  ∀ {root : KWDartPort G}
    (p : (kwOrderedDartPortSplitGraph G
      (kwAngularPortOrder embedding)).Walk root root),
    (hp : p.IsCycle) →
      letI : NeZero p.darts.length :=
        ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
          (SimpleGraph.Walk.darts_eq_nil.not.mpr
            hp.not_nil))⟩
      kwLoopPhaseProduct (kwAngularSplitPhase embedding)
        (kwGraphCycleDartLoop p) = -1


end StatMech.FrontierA
