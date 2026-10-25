/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc47trifarms.lean -/

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
import Theorem.StatisticalMechanics.Code.Percolation.ArmReachComponentClose.Part4
import Theorem.StatisticalMechanics.Code.Walls.bc46funnelproof.Part6
import Def.StatisticalMechanics.Code.Walls.bc47trifarms.Part3
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc47_R_adj (k : ℤ) : (hypercubicLattice 2).Adj (bc47_R k) (bc47_R (k + 1)) := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp [bc47_R]

theorem bc47_x_adj_a1 : (hypercubicLattice 2).Adj bc47_x bc47_a1 := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp [bc47_x, bc47_a1]

theorem bc47_x_adj_a2 : (hypercubicLattice 2).Adj bc47_x bc47_a2 := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp [bc47_x, bc47_a2]

theorem bc47_x_adj_a3 : (hypercubicLattice 2).Adj bc47_x bc47_a3 := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp [bc47_x, bc47_a3]


theorem bc47_armEdge_open (i : Fin 3) : bc47_fakeConfig (bc47_armEdge i) = true := by
  classical
  rw [bc47_fakeConfig, if_pos ⟨i, rfl⟩]

theorem bc47_x_a1_open : bc47_fakeConfig s(bc47_x, bc47_a1) = true := bc47_armEdge_open 0

theorem bc47_x_a2_open : bc47_fakeConfig s(bc47_x, bc47_a2) = true := bc47_armEdge_open 1

theorem bc47_x_a3_open : bc47_fakeConfig s(bc47_x, bc47_a3) = true := bc47_armEdge_open 2


theorem bc47_R_edge_open (k : ℤ) (hk : 0 ≤ k) :
    bc47_fakeConfig s(bc47_R k, bc47_R (k + 1)) = true := by
  classical
  rw [bc47_fakeConfig]
  by_cases h : (∃ i : Fin 3, s(bc47_R k, bc47_R (k + 1)) = bc47_armEdge i)
  · rw [if_pos h]
  · rw [if_neg h, if_pos ⟨k, hk, rfl⟩]


theorem bc47_R_edge_connected (k : ℤ) (hk : 0 ≤ k) :
    Connected 2 bc47_fakeConfig (bc47_R k) (bc47_R (k + 1)) :=
  IsOpenEdge.connected ⟨bc47_R_adj k, bc47_R_edge_open k hk⟩


theorem bc47_x_connected_R (m : ℤ) (hm : 0 ≤ m) :
    Connected 2 bc47_fakeConfig bc47_x (bc47_R m) := by
  rw [bc47_x_eq_R0]
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, m = (j : ℤ) := ⟨m.toNat, by omega⟩
  clear hm
  induction j with
  | zero => simpa using connected_refl bc47_fakeConfig (bc47_R 0)
  | succ i ih =>
    have hi : (0 : ℤ) ≤ (i : ℤ) := by positivity
    have step : Connected 2 bc47_fakeConfig (bc47_R (i : ℤ)) (bc47_R ((i : ℤ) + 1)) :=
      bc47_R_edge_connected (i : ℤ) hi
    have hcast : ((i : ℤ) + 1) = ((i + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [hcast] at step
    exact (ih).trans step

theorem bc47_x_connected_a1 : Connected 2 bc47_fakeConfig bc47_x bc47_a1 :=
  IsOpenEdge.connected ⟨bc47_x_adj_a1, bc47_x_a1_open⟩

theorem bc47_x_connected_a2 : Connected 2 bc47_fakeConfig bc47_x bc47_a2 :=
  IsOpenEdge.connected ⟨bc47_x_adj_a2, bc47_x_a2_open⟩

theorem bc47_x_connected_a3 : Connected 2 bc47_fakeConfig bc47_x bc47_a3 :=
  IsOpenEdge.connected ⟨bc47_x_adj_a3, bc47_x_a3_open⟩

theorem bc47_R_outside_box (n : ℕ) : bc47_R (n + 1) ∉ box 2 n := by
  rw [mem_box, not_forall]
  refine ⟨0, ?_⟩
  rw [not_le]
  simp only [bc47_R, Matrix.cons_val_zero]
  omega


theorem bc47_a1_ambient_infinite : (cluster 2 bc47_fakeConfig bc47_a1).Infinite := by
  rw [cluster_infinite_iff]
  intro n
  refine ⟨bc47_R (n + 1), bc47_R_outside_box n, ?_⟩
  exact (bc47_x_connected_a1.symm).trans (bc47_x_connected_R (n + 1) (by positivity))

theorem bc47_a2_ambient_infinite : (cluster 2 bc47_fakeConfig bc47_a2).Infinite := by
  rw [cluster_infinite_iff]
  intro n
  refine ⟨bc47_R (n + 1), bc47_R_outside_box n, ?_⟩
  exact (bc47_x_connected_a2.symm).trans (bc47_x_connected_R (n + 1) (by positivity))

theorem bc47_a3_ambient_infinite : (cluster 2 bc47_fakeConfig bc47_a3).Infinite := by
  rw [cluster_infinite_iff]
  intro n
  refine ⟨bc47_R (n + 1), bc47_R_outside_box n, ?_⟩
  exact (bc47_x_connected_a3.symm).trans (bc47_x_connected_R (n + 1) (by positivity))


theorem bc47_arm_not_R_edge (a : Site 2)
    (ha : a = bc47_a1 ∨ a = bc47_a2 ∨ a = bc47_a3) (k : ℤ) (hk : 0 ≤ k) :
    a ∉ s(bc47_R k, bc47_R (k + 1)) := by
  
  
  have hne : ∀ j : ℤ, a ≠ bc47_R j ∨ j < 0 := by
    intro j
    rcases ha with rfl | rfl | rfl
    · left; intro h
      have h1 := congrArg (fun v : Site 2 => v 1) h
      simp [bc47_a1, bc47_R] at h1
    · left; intro h
      have h1 := congrArg (fun v : Site 2 => v 1) h
      simp [bc47_a2, bc47_R] at h1
    · 
      by_cases hj : j < 0
      · exact Or.inr hj
      · left; intro h
        have h0 := congrArg (fun v : Site 2 => v 0) h
        simp only [bc47_a3, bc47_R, Matrix.cons_val_zero] at h0
        omega
  rw [Sym2.mem_iff]
  push Not
  refine ⟨?_, ?_⟩
  · rcases hne k with h | h
    · exact h
    · omega
  · rcases hne (k + 1) with h | h
    · exact h
    · omega


theorem bc47_arm_isolated (a : Site 2)
    (ha : a = bc47_a1 ∨ a = bc47_a2 ∨ a = bc47_a3) (y : Site 2) :
    ¬ (openSubgraph 2 (removeSite bc47_x bc47_fakeConfig)).Adj a y := by
  classical
  intro hadj
  obtain ⟨_, hopen⟩ := hadj
  by_cases hx : bc47_x ∈ s(a, y)
  · rw [removeSite_apply_of_mem hx] at hopen; exact Bool.false_ne_true hopen
  · rw [removeSite_apply_of_notMem hx, bc47_fakeConfig] at hopen
    
    have hnotstub : ¬ (∃ i : Fin 3, s(a, y) = bc47_armEdge i) := by
      rintro ⟨i, hi⟩
      apply hx
      
      have : bc47_x ∈ bc47_armEdge i := by
        fin_cases i <;> · rw [bc47_armEdge]; simp
      rwa [← hi] at this
    have hnotray : ¬ (∃ k : ℤ, 0 ≤ k ∧ s(a, y) = s(bc47_R k, bc47_R (k + 1))) := by
      rintro ⟨k, hk, hek⟩
      have hamem : a ∈ s(a, y) := Sym2.mem_mk_left a y
      rw [hek] at hamem
      exact bc47_arm_not_R_edge a ha k hk hamem
    rw [if_neg hnotstub, if_neg hnotray] at hopen
    exact Bool.false_ne_true hopen


theorem bc47_arm_removeSite_finite (a : Site 2)
    (ha : a = bc47_a1 ∨ a = bc47_a2 ∨ a = bc47_a3) :
    (cluster 2 (removeSite bc47_x bc47_fakeConfig) a).Finite := by
  have hsub : cluster 2 (removeSite bc47_x bc47_fakeConfig) a ⊆ {a} := by
    intro y hy
    rw [mem_cluster] at hy
    obtain ⟨w⟩ := hy
    cases w with
    | nil => simp
    | @cons _ b _ hadj _ => exact absurd hadj (bc47_arm_isolated a ha b)
  exact (Set.finite_singleton _).subset hsub


theorem bc47_arms_removeSite_disconnected :
    ¬ Connected 2 (removeSite bc47_x bc47_fakeConfig) bc47_a1 bc47_a2 ∧
    ¬ Connected 2 (removeSite bc47_x bc47_fakeConfig) bc47_a1 bc47_a3 ∧
    ¬ Connected 2 (removeSite bc47_x bc47_fakeConfig) bc47_a2 bc47_a3 := by
  
  
  have key : ∀ a b : Site 2, (a = bc47_a1 ∨ a = bc47_a2 ∨ a = bc47_a3) →
      Connected 2 (removeSite bc47_x bc47_fakeConfig) a b → b = a := by
    intro a b ha hconn
    obtain ⟨w⟩ := hconn
    cases w with
    | nil => rfl
    | @cons _ c _ hadj _ => exact absurd hadj (bc47_arm_isolated a ha c)
  refine ⟨?_, ?_, ?_⟩
  · intro h; have heq := key bc47_a1 bc47_a2 (Or.inl rfl) h
    
    have : bc47_a2 1 = bc47_a1 1 := by rw [heq]
    simp [bc47_a1, bc47_a2] at this
  · intro h; have heq := key bc47_a1 bc47_a3 (Or.inl rfl) h
    
    have : bc47_a3 0 = bc47_a1 0 := by rw [heq]
    simp [bc47_a1, bc47_a3] at this
  · intro h; have heq := key bc47_a2 bc47_a3 (Or.inr (Or.inl rfl)) h
    
    have : bc47_a3 0 = bc47_a2 0 := by rw [heq]
    simp [bc47_a2, bc47_a3] at this


theorem bc47_arms_distinct : bc47_a1 ≠ bc47_a2 ∧ bc47_a1 ≠ bc47_a3 ∧ bc47_a2 ≠ bc47_a3 := by
  refine ⟨?_, ?_, ?_⟩
  · intro h; have hc : bc47_a1 1 = bc47_a2 1 := by rw [h]
    simp [bc47_a1, bc47_a2] at hc
  · intro h; have hc : bc47_a1 0 = bc47_a3 0 := by rw [h]
    simp [bc47_a1, bc47_a3] at hc
  · intro h; have hc : bc47_a2 0 = bc47_a3 0 := by rw [h]
    simp [bc47_a2, bc47_a3] at hc


theorem bc47_isTrifurcation_fakeConfig :
    IsTrifurcation 2 bc47_fakeConfig bc47_x := by
  refine ⟨bc47_a1, bc47_a2, bc47_a3, bc47_arms_distinct,
    ⟨bc47_x_connected_a1, bc47_x_connected_a2, bc47_x_connected_a3⟩,
    ⟨bc47_a1_ambient_infinite, bc47_a2_ambient_infinite, bc47_a3_ambient_infinite⟩,
    bc47_arms_removeSite_disconnected⟩


theorem bc47_isTrifurcation_not_threeRemoveSiteInfiniteArms :
    ∃ (ω : ConfigSpace (Sym2 (Site 2))) (x : Site 2),
      IsTrifurcation 2 ω x ∧
      ∃ a₁ a₂ a₃ : Site 2,
        (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧
        (Connected 2 ω x a₁ ∧ Connected 2 ω x a₂ ∧ Connected 2 ω x a₃) ∧
        ((cluster 2 ω a₁).Infinite ∧ (cluster 2 ω a₂).Infinite ∧ (cluster 2 ω a₃).Infinite) ∧
        (¬ Connected 2 (removeSite x ω) a₁ a₂ ∧
         ¬ Connected 2 (removeSite x ω) a₁ a₃ ∧
         ¬ Connected 2 (removeSite x ω) a₂ a₃) ∧
        
        (¬ (cluster 2 (removeSite x ω) a₁).Infinite ∧
         ¬ (cluster 2 (removeSite x ω) a₂).Infinite ∧
         ¬ (cluster 2 (removeSite x ω) a₃).Infinite) :=
  ⟨bc47_fakeConfig, bc47_x, bc47_isTrifurcation_fakeConfig,
    bc47_a1, bc47_a2, bc47_a3, bc47_arms_distinct,
    ⟨bc47_x_connected_a1, bc47_x_connected_a2, bc47_x_connected_a3⟩,
    ⟨bc47_a1_ambient_infinite, bc47_a2_ambient_infinite, bc47_a3_ambient_infinite⟩,
    bc47_arms_removeSite_disconnected,
    ⟨fun h => h (bc47_arm_removeSite_finite bc47_a1 (Or.inl rfl)),
     fun h => h (bc47_arm_removeSite_finite bc47_a2 (Or.inr (Or.inl rfl))),
     fun h => h (bc47_arm_removeSite_finite bc47_a3 (Or.inr (Or.inr rfl)))⟩⟩


end StatMech.Walls
