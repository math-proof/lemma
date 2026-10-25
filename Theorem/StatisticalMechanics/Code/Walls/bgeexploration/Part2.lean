/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgeexploration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bfggenuinecarrier.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc64coarseembed.Part5
import Def.StatisticalMechanics.Code.Walls.bgeexploration
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


open Classical in


theorem bge_exploration_of_armComponents (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {z₀ z₁ : Site d} (hz₀ : z₀ ∈ vertexBoundary d R) (hz₁ : z₁ ∈ vertexBoundary d R)
    (hzne : z₀ ≠ z₁) (h : bge_ArmComponents ω L R) :
    bfg_GenuineExploration ω L R := by
  classical
  set Tf := btr_genuineTrifFinset ω L R with hTf
  rcases Finset.eq_empty_or_nonempty Tf with hemp | hne
  · 
    apply bfg_exploration_of_noTrif ω L R hz₀ hz₁ hzne
    intro y hybox hgen
    have : y ∈ Tf := by rw [hTf, bgt_mem_genuineTrifFinset]; exact ⟨hybox, hgen⟩
    rw [hemp] at this; exact absurd this (Finset.notMem_empty y)
  · 
    obtain ⟨comp, hcompB, hcompD⟩ := h
    have hTfne : Nonempty (↑Tf : Type) := hne.to_subtype
    obtain ⟨t0, ht0⟩ := hne
    let W := (↑Tf : Type) × Fin 4
    let ιT : Site d → W := fun y => if hy : y ∈ Tf then (⟨y, hy⟩, 0) else (⟨t0, ht0⟩, 0)
    refine ⟨W, inferInstance, ⟨(⟨t0, ht0⟩, 0)⟩, inferInstance, bc64_starForest (↑Tf : Type),
      inferInstance, ιT, comp, bc64_starForest_acyclic _, ?_, ?_, ?_, ?_, ?_⟩
    · 
      intro v; obtain ⟨t, i⟩ := v; exact bc64_starForest_min_degree (t, i)
    · 
      intro y hybox hgen
      have hy : y ∈ Tf := by rw [hTf, bgt_mem_genuineTrifFinset]; exact ⟨hybox, hgen⟩
      have hιT : ιT y = (⟨y, hy⟩, (0 : Fin 4)) := dif_pos hy
      rw [hιT, bc64_starForest_degree, bc64_starG_centre_deg]
    · 
      intro y hybox hgen z hzbox hgenz hyz
      have hy : y ∈ Tf := by rw [hTf, bgt_mem_genuineTrifFinset]; exact ⟨hybox, hgen⟩
      have hz : z ∈ Tf := by rw [hTf, bgt_mem_genuineTrifFinset]; exact ⟨hzbox, hgenz⟩
      simp only [ιT, dif_pos hy, dif_pos hz] at hyz
      exact Subtype.ext_iff.mp (Prod.ext_iff.mp hyz).1
    · 
      intro v hv; obtain ⟨t, i⟩ := v
      rw [bc64_starForest_deg1_iff] at hv
      exact hcompB (t, i) hv
    · 
      intro u hu v hv huv
      obtain ⟨t1, i1⟩ := u; obtain ⟨t2, i2⟩ := v
      rw [bc64_starForest_deg1_iff] at hu hv
      exact hcompD (t1, i1) hu (t2, i2) hv huv


theorem bge_exploration_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {z₀ z₁ : Site d} (hz₀ : z₀ ∈ vertexBoundary d R) (hz₁ : z₁ ∈ vertexBoundary d R)
    (hzne : z₀ ≠ z₁) (hno : ∀ y, y ∈ box d R → ¬ btr_IsGenuineCoarseTrif ω L y) :
    bfg_GenuineExploration ω L R :=
  bfg_exploration_of_noTrif ω L R hz₀ hz₁ hzne hno


theorem bge_bc60_exploration (L R : ℕ)
    {z₀ z₁ : Site 2} (hz₀ : z₀ ∈ vertexBoundary 2 R) (hz₁ : z₁ ∈ vertexBoundary 2 R)
    (hzne : z₀ ≠ z₁) :
    bfg_GenuineExploration bc60_upperLines L R :=
  bfg_bc60_exploration L R hz₀ hz₁ hzne


theorem bge_status :
    
    (∀ {ω : ConfigSpace (Sym2 (Site d))} {L : ℕ} {y a₁ a₂ a₃ : Site d},
      (¬ Connected d (removeSites (bc61_boxAround d L y) ω) a₁ a₂ ∧
       ¬ Connected d (removeSites (bc61_boxAround d L y) ω) a₁ a₃ ∧
       ¬ Connected d (removeSites (bc61_boxAround d L y) ω) a₂ a₃) →
      Disjoint (cluster d (removeSites (bc61_boxAround d L y) ω) a₁)
        (cluster d (removeSites (bc61_boxAround d L y) ω) a₂)) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (y : Site d),
      btr_IsGenuineCoarseTrif ω L y →
      (∀ z, z ∈ box d R → btr_IsGenuineCoarseTrif ω L z → z = y) →
      (∀ a : Site d,
        (∃ b ∈ bc61_boxAround d L y, (openSubgraph d ω).Adj b a) →
        Connected d ω y a →
        (cluster d (removeSites (bc61_boxAround d L y) ω) a).Infinite →
        (cluster d (removeSites (bc61_boxAround d L y) ω) a ∩ vertexBoundary d R).Nonempty) →
      bfg_GenuineExploration ω L R) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (z₀ z₁ : Site d),
      z₀ ∈ vertexBoundary d R → z₁ ∈ vertexBoundary d R → z₀ ≠ z₁ →
      bge_ArmComponents ω L R → bfg_GenuineExploration ω L R) := by
  refine ⟨fun hsep => bge_cluster_disjoint_of_notConnected hsep.1,
    fun ω L R y hy huniq hbdry => bge_exploration_of_singleGenuineTrif ω L R y hy huniq hbdry,
    ?_⟩
  intro ω L R z₀ z₁ hz₀ hz₁ hzne h
  exact bge_exploration_of_armComponents ω L R hz₀ hz₁ hzne h

end StatMech.Walls
