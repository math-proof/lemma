/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc117mergeproof.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc115severance.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc34ray.Part4
import Def.StatisticalMechanics.Code.Walls.bc117mergeproof
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.style.multiGoal false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc117_merge_of_boxAdjacentExternalArm {L n : ℕ}
    (harm : bc117_BoxAdjacentExternalArm d L n) :
    bc115_CoarseTrifMerge d L n := by
  intro ω hω x₁ x₂ x₃ hb₁ hb₂ hb₃ hi₁ hi₂ hi₃ hd₁₂ hd₁₃ hd₂₃
  obtain ⟨a₁, a₂, a₃, hadj₁, hadj₂, hadj₃, hinf₁, hinf₂, hinf₃, he₁, he₂, he₃⟩ :=
    harm ω hω x₁ x₂ x₃ hb₁ hb₂ hb₃ hi₁ hi₂ hi₃ hd₁₂ hd₁₃ hd₂₃
  refine ⟨∅, ?_⟩
  rw [bc115_forceOpen_empty]
  
  have hda₁₂ : cluster d ω a₁ ≠ cluster d ω a₂ := by rw [← he₁, ← he₂]; exact hd₁₂
  have hda₁₃ : cluster d ω a₁ ≠ cluster d ω a₃ := by rw [← he₁, ← he₃]; exact hd₁₃
  have hda₂₃ : cluster d ω a₂ ≠ cluster d ω a₃ := by rw [← he₂, ← he₃]; exact hd₂₃
  exact ⟨a₁, a₂, a₃, hadj₁, hadj₂, hadj₃, ⟨hinf₁, hinf₂, hinf₃⟩,
    ⟨bc115_disconnected_of_distinctClusters _ ω hda₁₂,
     bc115_disconnected_of_distinctClusters _ ω hda₁₃,
     bc115_disconnected_of_distinctClusters _ ω hda₂₃⟩⟩


theorem bc117_shell_of_walk_into_box {L : ℕ} {ω : ConfigSpace (Sym2 (Site 2))} {b u x : Site 2}
    (w : (openSubgraph 2 ω).Walk u x) :
    Connected 2 (removeSites (bc61_boxAround 2 L 0) ω) b u → u ∉ bc61_boxAround 2 L 0 →
    x ∈ bc61_boxAround 2 L 0 →
    ∃ s t : Site 2, (openSubgraph 2 ω).Adj s t ∧
      t ∈ bc61_boxAround 2 L 0 ∧
      Connected 2 (removeSites (bc61_boxAround 2 L 0) ω) b s := by
  induction w with
  | nil =>
    intro _ hu hx; exact absurd hx hu
  | @cons u v z hadj w' ih =>
    intro hbu hu hx
    by_cases hv : v ∈ bc61_boxAround 2 L 0
    · 
      exact ⟨u, v, hadj, hv, hbu⟩
    · 
      have hstep : Connected 2 (removeSites (bc61_boxAround 2 L 0) ω) u v :=
        bc117_cut_step_of_notMem hadj hu hv
      exact ih (hbu.trans hstep) hv hx


theorem bc117_attach_of_meetsBox {L : ℕ} {ω : ConfigSpace (Sym2 (Site 2))} {x x' : Site 2}
    (hinf : (cluster 2 ω x).Infinite) (hx'box : x' ∈ bc61_boxAround 2 L 0)
    (hxx' : cluster 2 ω x = cluster 2 ω x') :
    ∃ a : Site 2,
      (∃ bx ∈ bc61_boxAround 2 L 0, (openSubgraph 2 ω).Adj bx a) ∧
      (cluster 2 (removeSites (bc61_boxAround 2 L 0) ω) a).Infinite ∧
      cluster 2 ω x = cluster 2 ω a := by
  classical
  
  obtain ⟨b, hbconn, hbnot, hbinf⟩ :=
    bc117_boxAvoiding_external_infinite ω hinf (bc61_boxAround 2 L 0)
  
  have hxx'conn : Connected 2 ω x x' := by
    have : x' ∈ cluster 2 ω x := by rw [hxx']; exact self_mem_cluster ω x'
    exact mem_cluster.mp this
  have hbx' : Connected 2 ω b x' := hbconn.symm.trans hxx'conn
  obtain ⟨w⟩ := hbx'
  
  obtain ⟨s, t, hadj, htbox, hscut⟩ :=
    bc117_shell_of_walk_into_box (b := b) w (connected_refl _ b) hbnot hx'box
  refine ⟨s, ⟨t, htbox, hadj.symm⟩, ?_, ?_⟩
  · 
    have hcl : cluster 2 (removeSites (bc61_boxAround 2 L 0) ω) b
        = cluster 2 (removeSites (bc61_boxAround 2 L 0) ω) s :=
      cluster_eq_of_connected hscut
    rwa [hcl] at hbinf
  · 
    have hbs : Connected 2 ω b s := bc61_connected_of_cut hscut
    have : Connected 2 ω x s := hbconn.trans hbs
    exact cluster_eq_of_connected this


theorem bc117_merge_of_clustersMeetBox {L n : ℕ}
    (hmeet : ∀ ω ∈ threeMeetBox 2 n, ∀ x₁ x₂ x₃ : Site 2,
      x₁ ∈ box 2 n → x₂ ∈ box 2 n → x₃ ∈ box 2 n →
      (cluster 2 ω x₁).Infinite → (cluster 2 ω x₂).Infinite → (cluster 2 ω x₃).Infinite →
      cluster 2 ω x₁ ≠ cluster 2 ω x₂ → cluster 2 ω x₁ ≠ cluster 2 ω x₃ →
      cluster 2 ω x₂ ≠ cluster 2 ω x₃ →
      ∃ x₁' x₂' x₃' : Site 2,
        x₁' ∈ bc61_boxAround 2 L 0 ∧ x₂' ∈ bc61_boxAround 2 L 0 ∧ x₃' ∈ bc61_boxAround 2 L 0 ∧
        cluster 2 ω x₁ = cluster 2 ω x₁' ∧ cluster 2 ω x₂ = cluster 2 ω x₂' ∧
        cluster 2 ω x₃ = cluster 2 ω x₃') :
    bc115_CoarseTrifMerge 2 L n := by
  intro ω hω x₁ x₂ x₃ hb₁ hb₂ hb₃ hi₁ hi₂ hi₃ hd₁₂ hd₁₃ hd₂₃
  obtain ⟨x₁', x₂', x₃', hm₁, hm₂, hm₃, hc₁, hc₂, hc₃⟩ :=
    hmeet ω hω x₁ x₂ x₃ hb₁ hb₂ hb₃ hi₁ hi₂ hi₃ hd₁₂ hd₁₃ hd₂₃
  obtain ⟨a₁, hadj₁, hinf₁, he₁⟩ := bc117_attach_of_meetsBox hi₁ hm₁ hc₁
  obtain ⟨a₂, hadj₂, hinf₂, he₂⟩ := bc117_attach_of_meetsBox hi₂ hm₂ hc₂
  obtain ⟨a₃, hadj₃, hinf₃, he₃⟩ := bc117_attach_of_meetsBox hi₃ hm₃ hc₃
  refine ⟨∅, ?_⟩
  rw [bc115_forceOpen_empty]
  have hda₁₂ : cluster 2 ω a₁ ≠ cluster 2 ω a₂ := by rw [← he₁, ← he₂]; exact hd₁₂
  have hda₁₃ : cluster 2 ω a₁ ≠ cluster 2 ω a₃ := by rw [← he₁, ← he₃]; exact hd₁₃
  have hda₂₃ : cluster 2 ω a₂ ≠ cluster 2 ω a₃ := by rw [← he₂, ← he₃]; exact hd₂₃
  exact ⟨a₁, a₂, a₃, hadj₁, hadj₂, hadj₃, ⟨hinf₁, hinf₂, hinf₃⟩,
    ⟨bc115_disconnected_of_distinctClusters _ ω hda₁₂,
     bc115_disconnected_of_distinctClusters _ ω hda₁₃,
     bc115_disconnected_of_distinctClusters _ ω hda₂₃⟩⟩


theorem bc117_merge_of_le {L n : ℕ} (hnL : n ≤ L) : bc115_CoarseTrifMerge 2 L n := by
  apply bc117_merge_of_clustersMeetBox
  intro ω hω x₁ x₂ x₃ hb₁ hb₂ hb₃ hi₁ hi₂ hi₃ hd₁₂ hd₁₃ hd₂₃
  have hsub : box 2 n ⊆ box 2 L := box_mono 2 hnL
  refine ⟨x₁, x₂, x₃, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · rw [bc61_mem_boxAround_zero]; exact hsub hb₁
  · rw [bc61_mem_boxAround_zero]; exact hsub hb₂
  · rw [bc61_mem_boxAround_zero]; exact hsub hb₃


theorem bc117_engine_fires_upperLines {h : ℤ} (hh : 1 ≤ h) (L : ℕ) :
    ∃ b : Site 2, Connected 2 bc60_upperLines (bc57_pt 0 h) b ∧
      b ∉ bc61_boxAround 2 L 0 ∧
      (cluster 2 (removeSites (bc61_boxAround 2 L 0) bc60_upperLines) b).Infinite :=
  bc117_boxAvoiding_external_infinite bc60_upperLines (bc60_cluster_infinite hh)
    (bc61_boxAround 2 L 0)


theorem bc117_arm_shape_upperLines {L : ℕ} (hL : 3 ≤ L) :
    ∃ a₁ a₂ a₃ : Site 2,
      (∃ b₁ ∈ bc61_boxAround 2 L 0, (openSubgraph 2 bc60_upperLines).Adj b₁ a₁) ∧
      (∃ b₂ ∈ bc61_boxAround 2 L 0, (openSubgraph 2 bc60_upperLines).Adj b₂ a₂) ∧
      (∃ b₃ ∈ bc61_boxAround 2 L 0, (openSubgraph 2 bc60_upperLines).Adj b₃ a₃) ∧
      (cluster 2 (removeSites (bc61_boxAround 2 L 0) bc60_upperLines) a₁).Infinite ∧
      (cluster 2 (removeSites (bc61_boxAround 2 L 0) bc60_upperLines) a₂).Infinite ∧
      (cluster 2 (removeSites (bc61_boxAround 2 L 0) bc60_upperLines) a₃).Infinite := by
  refine ⟨bc57_pt ((L : ℤ) + 1) 1, bc57_pt ((L : ℤ) + 1) 2, bc57_pt ((L : ℤ) + 1) 3,
    bc61_upperLines_arm_boxAdjacent (by norm_num) (by exact_mod_cast (by omega : (1:ℤ) ≤ L)),
    bc61_upperLines_arm_boxAdjacent (by norm_num) (by exact_mod_cast (by omega : (2:ℤ) ≤ L)),
    bc61_upperLines_arm_boxAdjacent (by norm_num) (by exact_mod_cast (by omega : (3:ℤ) ≤ L)),
    bc61_upperLines_rightArm_infinite (by norm_num),
    bc61_upperLines_rightArm_infinite (by norm_num),
    bc61_upperLines_rightArm_infinite (by norm_num)⟩


end StatMech.Walls
