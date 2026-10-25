/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PlanarTopology.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Def.StatisticalMechanics.Code.Lattice.PlanarTopology.Part2
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

@[simp] theorem l1dist_self (d : ℕ) (x : Site d) : l1dist d x x = 0 := by
  unfold l1dist; simp

theorem l1dist_comm (d : ℕ) (x y : Site d) : l1dist d x y = l1dist d y x := by
  unfold l1dist
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Int.natAbs_neg, neg_sub]


theorem l1dist_of_adj (d : ℕ) {x y : Site d} (h : (hypercubicLattice d).Adj x y) :
    l1dist d x y = 1 := h


theorem l1dist_triangle (d : ℕ) (x y z : Site d) :
    l1dist d x z ≤ l1dist d x y + l1dist d y z := by
  unfold l1dist
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have hsplit : (x i - z i) = (x i - y i) + (y i - z i) := by ring
  rw [hsplit]
  exact Int.natAbs_add_le _ _


theorem l1dist_le_walk_length (d : ℕ) {x y : Site d}
    (w : (hypercubicLattice d).Walk x y) : l1dist d x y ≤ w.length := by
  induction w with
  | nil => simp
  | cons h p ih =>
    rename_i u v z
    rw [SimpleGraph.Walk.length_cons]
    calc l1dist d u z ≤ l1dist d u v + l1dist d v z := l1dist_triangle d u v z
      _ = 1 + l1dist d v z := by rw [l1dist_of_adj d h]
      _ ≤ 1 + p.length := Nat.add_le_add_left ih 1
      _ = p.length + 1 := by ring


theorem mem_support_l1dist_le (d : ℕ) {x y : Site d}
    (w : (hypercubicLattice d).Walk x y) {z : Site d} (hz : z ∈ w.support) :
    l1dist d x z ≤ w.length := by
  induction w with
  | nil =>
    simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
    subst hz; simp
  | cons h p ih =>
    rename_i u v t
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
    rw [SimpleGraph.Walk.length_cons]
    rcases hz with rfl | hz
    · simp
    · calc l1dist d u z ≤ l1dist d u v + l1dist d v z := l1dist_triangle d u v z
        _ = 1 + l1dist d v z := by rw [l1dist_of_adj d h]
        _ ≤ 1 + p.length := Nat.add_le_add_left (ih hz) 1
        _ = p.length + 1 := by ring


theorem circuit_support_subset_ball (d n : ℕ) (v : Site d)
    (w : (hypercubicLattice d).Walk v v) (hw : w.length = n) :
    ∀ z ∈ w.support, l1dist d v z ≤ n := by
  intro z hz
  rw [← hw]
  exact mem_support_l1dist_le d w hz

end Lattice
end StatMech
