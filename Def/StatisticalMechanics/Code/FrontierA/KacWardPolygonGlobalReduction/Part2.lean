/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonGlobalReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardFinitePolygonEar.Part12
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardUnitCycleReduction
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPolygonGlobalReduction.Part2
open scoped BigOperators
open Finset SimpleGraph Polynomial


namespace StatMech.FrontierA

open StatMech.Onsager

open StatMech.Ising

universe u


def KWStraightLineCycleOddTurning
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) : Prop :=
  ∀ {root : V} (p : G.Walk root root) (hp : p.IsCycle),
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    ∃ winding : ℤ,
      (∑ k, (embedding.dartAngle (kwGraphCycleDartLoop p (k + 1)) -
          embedding.dartAngle (kwGraphCycleDartLoop p k)).toReal : ℝ) =
        (winding : ℝ) * (2 * Real.pi) ∧
      Odd winding


end StatMech.FrontierA
