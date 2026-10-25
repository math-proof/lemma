/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ArmReachComponentClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneUniqueness.Part3
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationCount.Part6
import Theorem.StatisticalMechanics.Code.Percolation.SingleLeafHallClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.SecondPeelingClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.SpanForestArmsClose.Part2
import Def.StatisticalMechanics.Code.Percolation.ArmReachComponentClose.Part3
open Set SimpleGraph Finset
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem arc_ray_open (k : ℤ) (hk : -1 ≤ k) :
    arc_rayConfig s(arc_p k, arc_p (k + 1)) = true := by
  classical
  rw [arc_rayConfig, if_pos]; exact ⟨k, hk, rfl⟩

theorem arc_ray_edge_connected (k : ℤ) (hk : -1 ≤ k) :
    Connected 2 arc_rayConfig (arc_p k) (arc_p (k + 1)) :=
  IsOpenEdge.connected ⟨arc_p_adj k, arc_ray_open k hk⟩


theorem arc_ray_connected (m : ℤ) (hm : -1 ≤ m) :
    Connected 2 arc_rayConfig (arc_p (-1)) (arc_p m) := by
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, m = -1 + j := ⟨(m + 1).toNat, by omega⟩
  clear hm
  induction j with
  | zero => simpa using connected_refl arc_rayConfig (arc_p (-1))
  | succ i ih =>
    have hi : (-1 : ℤ) ≤ -1 + i := by omega
    have step : Connected 2 arc_rayConfig (arc_p (-1 + i)) (arc_p (-1 + (i : ℤ) + 1)) :=
      arc_ray_edge_connected (-1 + i) hi
    have hcast : (-1 : ℤ) + (i + 1 : ℕ) = (-1 + (i : ℤ)) + 1 := by push_cast; ring
    rw [hcast]
    exact (ih).trans step

theorem arc_p_outside_box (n : ℕ) : arc_p (n + 1) ∉ box 2 n := by
  rw [mem_box]; rw [not_forall]
  refine ⟨0, ?_⟩
  rw [not_le]
  simp only [arc_p, Matrix.cons_val_zero]
  have h1 : (0 : ℤ) ≤ (n : ℤ) + 1 := by positivity
  have h2 : ((n : ℤ) + 1).natAbs = (n + 1 : ℕ) := by omega
  omega


theorem arc_arm_ambient_infinite : (cluster 2 arc_rayConfig (arc_p (-1))).Infinite := by
  rw [cluster_infinite_iff]
  intro n
  exact ⟨arc_p (n + 1), arc_p_outside_box n, arc_ray_connected (n + 1) (by omega)⟩


theorem arc_armNeighbour_isolated (y : Site 2) :
    ¬ (openSubgraph 2 (removeSite (arc_p 0) arc_rayConfig)).Adj (arc_p (-1)) y := by
  classical
  intro hadj
  obtain ⟨_, hopen⟩ := hadj
  by_cases hx : arc_p 0 ∈ s(arc_p (-1), y)
  · rw [removeSite_apply_of_mem hx] at hopen; exact Bool.false_ne_true hopen
  · rw [removeSite_apply_of_notMem hx] at hopen
    rw [arc_rayConfig] at hopen
    split at hopen
    · rename_i hex
      obtain ⟨k, hk, hek⟩ := hex
      rw [Sym2.eq_iff] at hek
      rcases hek with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hkeq : (-1 : ℤ) = k := arc_p_inj h1
        rw [← hkeq] at h2
        apply hx
        rw [Sym2.mem_iff]; right
        rw [h2]; norm_num
      · have : (-1 : ℤ) = k + 1 := arc_p_inj h1
        omega
    · exact Bool.false_ne_true hopen


theorem arc_arm_removeSite_finite :
    (cluster 2 (removeSite (arc_p 0) arc_rayConfig) (arc_p (-1))).Finite := by
  have hsub : cluster 2 (removeSite (arc_p 0) arc_rayConfig) (arc_p (-1)) ⊆ {arc_p (-1)} := by
    intro y hy
    rw [mem_cluster] at hy
    obtain ⟨w⟩ := hy
    cases w with
    | nil => simp
    | @cons _ b _ hadj _ => exact absurd hadj (arc_armNeighbour_isolated b)
  exact (Set.finite_singleton _).subset hsub


theorem arc_arm_adj_x : (openSubgraph 2 arc_rayConfig).Adj (arc_p 0) (arc_p (-1)) := by
  have h : arc_rayConfig s(arc_p (-1), arc_p 0) = true := by
    have := arc_ray_open (-1) (by norm_num); simpa using this
  refine ⟨?_, ?_⟩
  · rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp [arc_p]
  · rw [Sym2.eq_swap]; exact h


theorem arc_ambientInfinite_not_removeSiteInfinite :
    ∃ (ω : ConfigSpace (Sym2 (Site 2))) (x a : Site 2),
      (openSubgraph 2 ω).Adj x a ∧
      Connected 2 ω x a ∧
      (cluster 2 ω a).Infinite ∧
      ¬ (cluster 2 (removeSite x ω) a).Infinite :=
  ⟨arc_rayConfig, arc_p 0, arc_p (-1), arc_arm_adj_x, arc_arm_adj_x.reachable,
    arc_arm_ambient_infinite, fun hinf => hinf arc_arm_removeSite_finite⟩

end Percolation
end StatMech
