/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TwoPoint.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.FK.FKG
import Theorem.StatisticalMechanics.Code.Inequalities.IncreasingEvent.Part2
import Instance.StatisticalMechanics.Code.FK.TwoPoint
open scoped BigOperators
open SimpleGraph


namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in


@[simp]
theorem connEvent_self (x : V) : connEvent G x x = Set.univ := by
  ext ω
  simp only [mem_connEvent, Set.mem_univ, iff_true]
  exact SimpleGraph.Reachable.refl x

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in


theorem connEvent_isIncreasing (x y : V) : IsIncreasing (connEvent G x y) := by
  intro a b hab ha
  simp only [mem_connEvent] at ha ⊢
  exact ha.mono (openSub_mono G hab)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in


theorem allOpen_mem_connEvent {x y : V} (h : G.Reachable x y) :
    (fun _ => true) ∈ connEvent G x y := by
  have hG : openSub G (fun _ => true) = G := by ext a b; simp [openSub_adj]
  rw [mem_connEvent, hG]
  exact h


end FK
end StatMech
