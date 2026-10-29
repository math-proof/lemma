/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc56menger.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc55route
import Theorem.StatisticalMechanics.Code.Percolation.BoxMergeFreeMenger.Part2
import Theorem.StatisticalMechanics.Code.Percolation.BoxMengerAttachment.Part3
import Theorem.StatisticalMechanics.Code.Percolation.ClusterReachesRay.Part3
import Theorem.StatisticalMechanics.Code.Percolation.CanonicalTrifCount.Part4
import Def.StatisticalMechanics.Code.Walls.bc56menger.Part4
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc56_offAxisLine_open (k : ℤ) :
    bc56_offAxisLine s(bc56_lp k, bc56_lp (k + 1)) = true := by
  classical
  rw [bc56_offAxisLine, if_pos]; exact ⟨k, rfl⟩


theorem bc56_offAxisLine_connected_pos (m : ℤ) (hm : 0 ≤ m) :
    Connected 2 bc56_offAxisLine (bc56_lp 0) (bc56_lp m) := by
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, m = (j : ℤ) := ⟨m.toNat, by omega⟩
  clear hm
  induction j with
  | zero => simpa using connected_refl _ (bc56_lp 0)
  | succ i ih =>
    have step : Connected 2 bc56_offAxisLine (bc56_lp (i : ℤ)) (bc56_lp ((i : ℤ) + 1)) :=
      IsOpenEdge.connected ⟨bc56_lp_adj (i : ℤ), bc56_offAxisLine_open (i : ℤ)⟩
    have hcast : ((i + 1 : ℕ) : ℤ) = (i : ℤ) + 1 := by push_cast; ring
    rw [hcast]; exact ih.trans step


theorem bc56_lp_pos_outside_box (m : ℕ) : bc56_lp (m + 1) ∉ box 2 m := by
  rw [mem_box]; simp only [not_forall, not_le]; refine ⟨0, ?_⟩
  simp only [bc56_lp, Matrix.cons_val_zero]
  have : ((m : ℤ) + 1).natAbs = (m + 1 : ℕ) := by omega
  omega


theorem bc56_offAxisLine_cluster_infinite :
    (cluster 2 bc56_offAxisLine (bc56_lp 0)).Infinite := by
  rw [cluster_infinite_iff]
  intro m
  exact ⟨bc56_lp (m + 1), bc56_lp_pos_outside_box m,
    bc56_offAxisLine_connected_pos ((m : ℤ) + 1) (by positivity)⟩


theorem bc56_lp_zero_mem_box : bc56_lp 0 ∈ box 2 2 := by
  rw [mem_box]; intro i; fin_cases i <;> simp [bc56_lp]


theorem bc56_offAxisLine_height_step {u v : Site 2} (_hu : u 1 = 2)
    (hadj : (openSubgraph 2 bc56_offAxisLine).Adj u v) : v 1 = 2 := by
  classical
  obtain ⟨_, hopen⟩ := hadj
  rw [bc56_offAxisLine] at hopen
  by_cases hk : ∃ k : ℤ, s(u, v) = s(bc56_lp k, bc56_lp (k + 1))
  · obtain ⟨k, hkeq⟩ := hk
    rw [Sym2.eq_iff] at hkeq
    rcases hkeq with ⟨_, hv⟩ | ⟨_, hv⟩ <;> rw [hv, bc56_lp_snd]
  · rw [if_neg hk] at hopen; exact absurd hopen (by decide)


theorem bc56_offAxisLine_height_invariant {u y : Site 2} (hu : u 1 = 2)
    (h : Connected 2 bc56_offAxisLine u y) : y 1 = 2 := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact hu
  | @cons a b c hab w' ih => exact ih (bc56_offAxisLine_height_step hu hab)


theorem bc56_offAxisLine_no_originNbr :
    ∀ a : Site 2, (hypercubicLattice 2).Adj 0 a → a ∉ cluster 2 bc56_offAxisLine (bc56_lp 0) := by
  intro a hadj hmem
  rw [mem_cluster] at hmem
  have ha2 : a 1 = 2 := bc56_offAxisLine_height_invariant (by simp [bc56_lp]) hmem
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
  
  have h1 : ((0 : Site 2) 1 - a 1).natAbs = 2 := by
    simp only [Pi.zero_apply, ha2]; decide
  omega


theorem bc56_offAxisLine_no_runsAlongAxis (j : Fin 2) :
    ¬ crr_ClusterRunsAlongAxis bc56_offAxisLine (bc56_lp 0) j := by
  intro h
  have hmem : hrHD_rayPt j 1 ∈ cluster 2 bc56_offAxisLine (bc56_lp 0) :=
    bc56_runsAlongAxis_forces_nbr_in_cluster bc56_offAxisLine (bc56_lp 0) j h
  exact bc56_offAxisLine_no_originNbr (hrHD_rayPt j 1) (hrHD_adj_origin_rayPt_one j) hmem


theorem bc56_status (hd : 1 ≤ d) (p : NNReal) (hp1 : p ≤ 1) (hp0 : 0 < p) :
    ((∀ n : ℕ, bc56_BoxClusterReachesNbr d n) →
      bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0) ∧
    (∀ j : Fin 2, ¬ crr_ClusterRunsAlongAxis bc56_offAxisLine (bc56_lp 0) j) :=
  ⟨fun h => (bc56_burton_keane_bernoulli_of_reachesNbr hd p hp1 hp0 h).2.1,
   bc56_offAxisLine_no_runsAlongAxis⟩

end StatMech.Walls
