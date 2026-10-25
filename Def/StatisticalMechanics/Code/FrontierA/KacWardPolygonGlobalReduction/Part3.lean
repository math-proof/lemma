/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonGlobalReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardFinitePolygonEar.Part12
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardUnitCycleReduction
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPolygonGlobalReduction.Part3
open scoped BigOperators
open Finset SimpleGraph Polynomial


namespace StatMech.FrontierA

open StatMech.Onsager

open StatMech.Ising

universe u


def KWStraightLineCycleTurning
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) : Prop :=
  ∀ {root : V} (p : G.Walk root root) (hp : p.IsCycle),
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    (∑ k, (embedding.dartAngle (kwGraphCycleDartLoop p (k + 1)) -
        embedding.dartAngle (kwGraphCycleDartLoop p k)).toReal : ℝ) =
        2 * Real.pi ∨
      (∑ k, (embedding.dartAngle (kwGraphCycleDartLoop p (k + 1)) -
        embedding.dartAngle (kwGraphCycleDartLoop p k)).toReal : ℝ) =
        -(2 * Real.pi)


end StatMech.FrontierA
