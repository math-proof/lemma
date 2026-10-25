/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardCycleCoefficient.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardUnitCycleReduction
import Def.StatisticalMechanics.Code.FrontierA.KacWardCycleCoefficient.Part2
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.FrontierA

open StatMech.Onsager

universe u


@[simp] theorem kwGraphLoopRev_apply
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {n : ℕ} [NeZero n] (loop : Fin n → G.Dart) (k : Fin n) :
    kwGraphLoopRev loop k = (loop (-k)).symm := rfl

theorem kwGraphLoopExponent_loopRev
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ} [NeZero n] (loop : Fin n → G.Dart) :
    kwGraphLoopExponent G (kwGraphLoopRev loop) =
      kwGraphLoopExponent G loop := by
  unfold kwGraphLoopExponent kwGraphLoopRev ons_involutiveLoopRev
  simp only [SimpleGraph.Dart.edge_symm]
  exact Equiv.sum_comp (Equiv.neg (Fin n))
    (fun k : Fin n ↦ Finsupp.single (loop k).edge 1)


theorem kwGraphLoopScalar_loopRev_straightLine
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    {n : ℕ} [NeZero n] (loop : Fin n → G.Dart) :
    kwGraphLoopScalar G embedding.turnPhase (kwGraphLoopRev loop) =
      kwGraphLoopScalar G embedding.turnPhase loop := by
  exact kwStraightLineGraphLoopWeight_loopRev G embedding (fun _ ↦ 1) loop


end StatMech.FrontierA
