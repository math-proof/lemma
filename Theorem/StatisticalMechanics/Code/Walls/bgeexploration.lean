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


theorem bge_cluster_disjoint_of_notConnected {ω' : ConfigSpace (Sym2 (Site d))} {a b : Site d}
    (h : ¬ Connected d ω' a b) : Disjoint (cluster d ω' a) (cluster d ω' b) := by
  rw [Set.disjoint_left]
  intro p hpa hpb
  rw [mem_cluster] at hpa hpb
  exact h (hpa.trans hpb.symm)


theorem bge_singleGenuineTrif_arms_disjoint {ω : ConfigSpace (Sym2 (Site d))} {L : ℕ} {y : Site d}
    {a₁ a₂ a₃ : Site d}
    (hsep : ¬ Connected d (removeSites (bc61_boxAround d L y) ω) a₁ a₂ ∧
            ¬ Connected d (removeSites (bc61_boxAround d L y) ω) a₁ a₃ ∧
            ¬ Connected d (removeSites (bc61_boxAround d L y) ω) a₂ a₃) :
    Disjoint (cluster d (removeSites (bc61_boxAround d L y) ω) a₁)
        (cluster d (removeSites (bc61_boxAround d L y) ω) a₂) ∧
    Disjoint (cluster d (removeSites (bc61_boxAround d L y) ω) a₁)
        (cluster d (removeSites (bc61_boxAround d L y) ω) a₃) ∧
    Disjoint (cluster d (removeSites (bc61_boxAround d L y) ω) a₂)
        (cluster d (removeSites (bc61_boxAround d L y) ω) a₃) :=
  ⟨bge_cluster_disjoint_of_notConnected hsep.1,
   bge_cluster_disjoint_of_notConnected hsep.2.1,
   bge_cluster_disjoint_of_notConnected hsep.2.2⟩

open Classical in


theorem bge_exploration_of_singleGenuineTrif (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (y : Site d)
    (hy : btr_IsGenuineCoarseTrif ω L y)
    (huniq : ∀ z, z ∈ box d R → btr_IsGenuineCoarseTrif ω L z → z = y)
    (hbdry : ∀ a : Site d,
      (∃ b ∈ bc61_boxAround d L y, (openSubgraph d ω).Adj b a) →
      Connected d ω y a →
      (cluster d (removeSites (bc61_boxAround d L y) ω) a).Infinite →
      (cluster d (removeSites (bc61_boxAround d L y) ω) a ∩ vertexBoundary d R).Nonempty) :
    bfg_GenuineExploration ω L R := by
  classical
  obtain ⟨a₁, a₂, a₃, ⟨b₁, hb1m, hb1a⟩, ⟨b₂, hb2m, hb2a⟩, ⟨b₃, hb3m, hb3a⟩,
    ⟨hcy1, hcy2, hcy3⟩, ⟨hi1, hi2, hi3⟩, hsep⟩ := hy
  set ω' := removeSites (bc61_boxAround d L y) ω with hω'
  
  set C₁ := cluster d ω' a₁ with hC1
  set C₂ := cluster d ω' a₂ with hC2
  set C₃ := cluster d ω' a₃ with hC3
  obtain ⟨hd12, hd13, hd23⟩ := bge_singleGenuineTrif_arms_disjoint (ω := ω) (L := L) (y := y) hsep
  refine ⟨Fin 4, inferInstance, inferInstance, inferInstance, bc64_starG, inferInstance,
    (fun _ => (0 : Fin 4)),
    (fun v => if v = 1 then C₁ else if v = 2 then C₂ else if v = 3 then C₃ else (∅ : Set (Site d))),
    bc64_starG_isTree.isAcyclic, ?_, ?_, ?_, ?_, ?_⟩
  · 
    intro v; fin_cases v <;> decide
  · 
    intro z _ _; exact bc64_starG_centre_deg.ge
  · 
    intro z hzbox hzgen z' hz'box hz'gen _
    rw [huniq z hzbox hzgen, huniq z' hz'box hz'gen]
  · 
    intro v hv
    fin_cases v <;>
      first
        | exact absurd hv (by decide)
        | exact hbdry a₁ ⟨b₁, hb1m, hb1a⟩ hcy1 hi1
        | exact hbdry a₂ ⟨b₂, hb2m, hb2a⟩ hcy2 hi2
        | exact hbdry a₃ ⟨b₃, hb3m, hb3a⟩ hcy3 hi3
  · 
    intro u hu v hv huv
    fin_cases u <;> fin_cases v <;>
      first
        | exact absurd hu (by decide)
        | exact absurd hv (by decide)
        | exact absurd rfl huv
        | exact hd12
        | exact hd12.symm
        | exact hd13
        | exact hd13.symm
        | exact hd23
        | exact hd23.symm


end StatMech.Walls
