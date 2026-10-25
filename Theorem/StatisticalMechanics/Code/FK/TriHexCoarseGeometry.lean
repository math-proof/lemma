/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexCoarseGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FK.PeriodicPlanarGraph.Part18
open Set SimpleGraph


namespace StatMech

namespace FK

namespace PeriodicPlanar

open Lattice


theorem triangular_reachable_axis_le
    (x : Site 2) (j : Fin 2) (a : Int) (n : Nat) :
    triangularGraph.Reachable (Function.update x j a)
      (Function.update x j (a + n)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      refine ih.trans (SimpleGraph.Adj.reachable ?_)
      rw [triangularGraph_adj]
      fin_cases j
      · refine ⟨0, Or.inl ?_⟩
        ext k
        fin_cases k <;> simp [triangularStep]
      · refine ⟨1, Or.inl ?_⟩
        ext k
        fin_cases k <;> simp [triangularStep]


theorem triangular_reachable_axis
    (x : Site 2) (j : Fin 2) (a b : Int) :
    triangularGraph.Reachable (Function.update x j a)
      (Function.update x j b) := by
  rcases le_total a b with hab | hab
  · obtain ⟨n, rfl⟩ := Int.le.dest hab
    exact triangular_reachable_axis_le x j a n
  · obtain ⟨n, rfl⟩ := Int.le.dest hab
    exact (triangular_reachable_axis_le x j b n).symm


theorem triangularGraph_connected : triangularGraph.Connected := by
  rw [SimpleGraph.connected_iff]
  refine ⟨?_, ⟨0⟩⟩
  intro x y
  have h0 : triangularGraph.Reachable x (Function.update x 0 (y 0)) := by
    have h := triangular_reachable_axis x 0 (x 0) (y 0)
    rwa [Function.update_eq_self] at h
  set z := Function.update x 0 (y 0) with hz
  have h1 : triangularGraph.Reachable z (Function.update z 1 (y 1)) := by
    have h := triangular_reachable_axis z 1 (z 1) (y 1)
    rwa [Function.update_eq_self] at h
  have hzy : Function.update z 1 (y 1) = y := by
    funext i
    fin_cases i <;> simp [hz]
  rw [hzy] at h1
  exact h0.trans h1


theorem triangular_adj_sub_mem_box_one
    {x y : Site 2} (hxy : triangularGraph.Adj x y) :
    y - x ∈ box 2 1 := by
  rw [triangularGraph_adj] at hxy
  obtain ⟨i, h | h⟩ := hxy
  · rw [h]
    intro j
    fin_cases i <;> fin_cases j <;> norm_num [triangularStep]
  · have hyx : y - x = -triangularStep i := by
      rw [← h]
      abel
    rw [hyx]
    intro j
    fin_cases i <;> fin_cases j <;> norm_num [triangularStep]


theorem triangular_walk_sub_mem_box
    {x y : Site 2} (w : triangularGraph.Walk x y) :
    y - x ∈ box 2 w.length := by
  induction w with
  | nil =>
      intro j
      simp
  | @cons x y z hxy w ih =>
      have hstep := triangular_adj_sub_mem_box_one hxy
      intro j
      have hsum : z j - x j = (z j - y j) + (y j - x j) := by omega
      simp only [Pi.sub_apply]
      rw [hsum]
      calc
        ((z j - y j) + (y j - x j)).natAbs ≤
            (z j - y j).natAbs + (y j - x j).natAbs :=
          Int.natAbs_add_le _ _
        _ ≤ w.length + 1 := Nat.add_le_add (ih j) (hstep j)
        _ = (Walk.cons hxy w).length := by simp [Nat.add_comm]


theorem triangular_sub_mem_box_dist (x y : Site 2) :
    y - x ∈ box 2 (triangularGraph.dist x y) := by
  obtain ⟨w, hw⟩ := triangularGraph_connected.exists_walk_length_eq_dist x y
  simpa [hw] using triangular_walk_sub_mem_box w


theorem exists_triangular_axis_walk_le
    (x : Site 2) (j : Fin 2) (a : Int) (n : Nat) :
    ∃ w : triangularGraph.Walk (Function.update x j a)
        (Function.update x j (a + n)), w.length = n := by
  induction n with
  | zero =>
      have hzero : Function.update x j (a + (0 : Nat)) =
          Function.update x j a := by simp
      rw [hzero]
      exact ⟨Walk.nil, rfl⟩
  | succ n ih =>
      obtain ⟨w, hw⟩ := ih
      have hadj : triangularGraph.Adj (Function.update x j (a + n))
          (Function.update x j (a + (n + 1))) := by
        rw [triangularGraph_adj]
        fin_cases j
        · refine ⟨0, Or.inl ?_⟩
          ext k
          fin_cases k <;> simp [triangularStep]
        · refine ⟨1, Or.inl ?_⟩
          ext k
          fin_cases k <;> simp [triangularStep]
      refine ⟨w.concat hadj, ?_⟩
      simp [hw]


theorem exists_triangular_axis_walk
    (x : Site 2) (j : Fin 2) (a b : Int) :
    ∃ w : triangularGraph.Walk (Function.update x j a)
        (Function.update x j b), w.length = (b - a).natAbs := by
  rcases le_total a b with hab | hab
  · obtain ⟨n, rfl⟩ := Int.le.dest hab
    obtain ⟨w, hw⟩ := exists_triangular_axis_walk_le x j a n
    refine ⟨w, ?_⟩
    simpa using hw
  · obtain ⟨n, rfl⟩ := Int.le.dest hab
    obtain ⟨w, hw⟩ := exists_triangular_axis_walk_le x j b n
    refine ⟨w.reverse, ?_⟩
    simpa using hw


theorem exists_triangular_axis_walk_from
    (x : Site 2) (j : Fin 2) (b : Int) :
    ∃ w : triangularGraph.Walk x (Function.update x j b),
      w.length = (b - x j).natAbs := by
  have h := exists_triangular_axis_walk x j (x j) b
  have hstart : Function.update x j (x j) = x := Function.update_eq_self _ _
  rw [hstart] at h
  exact h


theorem exists_triangular_coordinate_walk (x y : Site 2) :
    ∃ w : triangularGraph.Walk x y,
      w.length = (y 0 - x 0).natAbs + (y 1 - x 1).natAbs := by
  obtain ⟨w0, hw0⟩ := exists_triangular_axis_walk_from x 0 (y 0)
  let z := Function.update x 0 (y 0)
  change triangularGraph.Walk x z at w0
  obtain ⟨w1, hw1⟩ := exists_triangular_axis_walk_from z 1 (y 1)
  have hwalk : ∃ w : triangularGraph.Walk x (Function.update z 1 (y 1)),
      w.length = (y 0 - x 0).natAbs + (y 1 - x 1).natAbs := by
    refine ⟨w0.append w1, ?_⟩
    rw [Walk.length_append, hw0, hw1]
    simp [z]
  have hend : Function.update z 1 (y 1) = y := by
    funext i
    fin_cases i <;> simp [z]
  rw [hend] at hwalk
  exact hwalk


theorem triangular_dist_le_coordinate_sum (x y : Site 2) :
    triangularGraph.dist x y ≤
      (y 0 - x 0).natAbs + (y 1 - x 1).natAbs := by
  obtain ⟨w, hw⟩ := exists_triangular_coordinate_walk x y
  exact (SimpleGraph.dist_le w).trans_eq hw


theorem triangular_dist_le_two_mul_of_sub_mem_box
    {x y : Site 2} {n : Nat} (hxy : y - x ∈ box 2 n) :
    triangularGraph.dist x y ≤ 2 * n := by
  have h0 := hxy 0
  have h1 := hxy 1
  simp only [Pi.sub_apply] at h0 h1
  have hdist := triangular_dist_le_coordinate_sum x y
  omega


end PeriodicPlanar
end FK
end StatMech
