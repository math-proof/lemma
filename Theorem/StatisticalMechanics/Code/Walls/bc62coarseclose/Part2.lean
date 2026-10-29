/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc62coarseclose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc61coarsebox.Part5
import Theorem.StatisticalMechanics.Code.Walls.bc49finiteenergy
import Def.StatisticalMechanics.Code.Walls.bc62coarseclose
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc62_precursor_subset_force_coarseTrif (L : ℕ) (a₁ a₂ a₃ b₁ b₂ b₃ : Site d) :
    bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃ ⊆
      (fun ω => forceOpenFinset {s(b₁, a₁), s(b₂, a₂), s(b₃, a₃)} ω)
        ⁻¹' {ω | bc61_IsCoarseTrifurcation ω L 0} := by
  rintro ω ⟨⟨hb1, hb2, hb3⟩, ⟨hadj1, hadj2, hadj3⟩, ⟨hinf1, hinf2, hinf3⟩, ⟨hsep12, hsep13, hsep23⟩⟩
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  exact bc62_isCoarseTrifurcation_of_neighbors ω L a₁ a₂ a₃ b₁ b₂ b₃ hb1 hb2 hb3
    hadj1 hadj2 hadj3 hinf1 hinf2 hinf3 hsep12 hsep13 hsep23


theorem bc62_coarseTrif_of_precursor_mem (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ)
    (a₁ a₂ a₃ b₁ b₂ b₃ : Site d) (hω : ω ∈ bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃) :
    bc61_IsCoarseTrifurcation
      (forceOpenFinset {s(b₁, a₁), s(b₂, a₂), s(b₃, a₃)} ω) L 0 :=
  bc62_precursor_subset_force_coarseTrif L a₁ a₂ a₃ b₁ b₂ b₃ hω


theorem bc62_coarseTrif_pos_of_precursor_pos
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hfe : HasFiniteEnergyMerge μ) (L : ℕ) (a₁ a₂ a₃ b₁ b₂ b₃ : Site d)
    (hpos : 0 < μ (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃)) :
    0 < μ {ω | bc61_IsCoarseTrifurcation ω L 0} := by
  classical
  set F : Finset (Sym2 (Site d)) := {s(b₁, a₁), s(b₂, a₂), s(b₃, a₃)} with hFdef
  by_contra h
  rw [not_lt, nonpos_iff_eq_zero] at h
  have hac : (μ.map (fun ω => forceOpenFinset F ω)) ≪ μ := hfe F
  have hpush : (μ.map (fun ω => forceOpenFinset F ω)) {ω | bc61_IsCoarseTrifurcation ω L 0}
      = μ ((fun ω => forceOpenFinset F ω) ⁻¹' {ω | bc61_IsCoarseTrifurcation ω L 0}) :=
    Measure.map_apply (measurable_forceOpenFinset F) (bc62_measurableSet_coarseTrif L 0)
  have hpre0 : μ ((fun ω => forceOpenFinset F ω) ⁻¹' {ω | bc61_IsCoarseTrifurcation ω L 0}) = 0 := by
    rw [← hpush]; exact hac h
  have hAle : μ (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃)
      ≤ μ ((fun ω => forceOpenFinset F ω) ⁻¹' {ω | bc61_IsCoarseTrifurcation ω L 0}) :=
    measure_mono (bc62_precursor_subset_force_coarseTrif L a₁ a₂ a₃ b₁ b₂ b₃)
  rw [hpre0] at hAle
  exact absurd (le_antisymm hAle bot_le) (ne_of_gt hpos)


theorem bc62_coarseTrifExistence_of_route
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hfe : HasFiniteEnergyMerge μ) (L : ℕ)
    (hcoarseRoute : 0 < μ {ω | numInfiniteClusters d ω = ⊤} →
      ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site d,
        0 < μ (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃)) :
    bc61_CoarseTrifExistence μ L := by
  intro htop
  obtain ⟨a₁, a₂, a₃, b₁, b₂, b₃, hpre⟩ := hcoarseRoute htop
  exact bc62_coarseTrif_pos_of_precursor_pos μ hfe L a₁ a₂ a₃ b₁ b₂ b₃ hpre


theorem bc62_boxVertex_mem {L : ℕ} {h : ℤ} (hh : 1 ≤ h) (hhL : h ≤ (L : ℤ)) :
    bc57_pt (L : ℤ) h ∈ bc61_boxAround 2 L 0 := by
  rw [bc61_mem_boxAround_zero, mem_box]; intro i; fin_cases i
  · change ((bc57_pt (L : ℤ) h) 0).natAbs ≤ L; rw [bc57_pt_fst]; simp
  · change ((bc57_pt (L : ℤ) h) 1).natAbs ≤ L; rw [bc57_pt_snd]; omega


theorem bc62_upperLines_mem_coarsePrecursor {L : ℕ} (hL : 3 ≤ L) :
    bc60_upperLines ∈ bc62_CoarseTrifPrecursor 2 L
      (bc57_pt ((L : ℤ) + 1) 1) (bc57_pt ((L : ℤ) + 1) 2) (bc57_pt ((L : ℤ) + 1) 3)
      (bc57_pt (L : ℤ) 1) (bc57_pt (L : ℤ) 2) (bc57_pt (L : ℤ) 3) := by
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  
  · exact bc62_boxVertex_mem (by norm_num) (by exact_mod_cast (by omega : (1:ℤ) ≤ L))
  · exact bc62_boxVertex_mem (by norm_num) (by exact_mod_cast (by omega : (2:ℤ) ≤ L))
  · exact bc62_boxVertex_mem (by norm_num) (by exact_mod_cast (by omega : (3:ℤ) ≤ L))
  
  · exact bc57_pt_adj (L : ℤ) 1
  · exact bc57_pt_adj (L : ℤ) 2
  · exact bc57_pt_adj (L : ℤ) 3
  
  · exact bc61_upperLines_rightArm_infinite (by norm_num)
  · exact bc61_upperLines_rightArm_infinite (by norm_num)
  · exact bc61_upperLines_rightArm_infinite (by norm_num)
  
  · exact bc61_upperLines_arm_disconnected (by norm_num)
  · exact bc61_upperLines_arm_disconnected (by norm_num)
  · exact bc61_upperLines_arm_disconnected (by norm_num)


theorem bc62_upperLines_forced_coarseTrif {L : ℕ} (hL : 3 ≤ L) :
    bc61_IsCoarseTrifurcation
      (forceOpenFinset {s(bc57_pt (L : ℤ) 1, bc57_pt ((L : ℤ) + 1) 1),
        s(bc57_pt (L : ℤ) 2, bc57_pt ((L : ℤ) + 1) 2),
        s(bc57_pt (L : ℤ) 3, bc57_pt ((L : ℤ) + 1) 3)} bc60_upperLines) L 0 :=
  bc62_coarseTrif_of_precursor_mem bc60_upperLines L _ _ _ _ _ _
    (bc62_upperLines_mem_coarsePrecursor hL)


theorem bc62_status :
    
    (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))),
      IsTranslationInvariant (G := Multiplicative (Site 2)) μ → ∀ (L R : ℕ),
        ((boxFinsetBK 2 R).card : ENNReal) * μ {ω | bc61_IsCoarseTrifurcation ω L 0}
          = ∫⁻ ω, (bc61_coarseTcount ω L R : ENNReal) ∂μ) ∧
    
    (∀ {L : ℕ}, 3 ≤ L →
      bc60_upperLines ∈ bc62_CoarseTrifPrecursor 2 L
        (bc57_pt ((L : ℤ) + 1) 1) (bc57_pt ((L : ℤ) + 1) 2) (bc57_pt ((L : ℤ) + 1) 3)
        (bc57_pt (L : ℤ) 1) (bc57_pt (L : ℤ) 2) (bc57_pt (L : ℤ) 3)) :=
  ⟨fun μ hinv L R => bc62_coarse_expectation μ hinv L R,
   fun hL => bc62_upperLines_mem_coarsePrecursor hL⟩


theorem bc62_infiniteClusters_top_null_of_forest_route
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ] (hd : 1 ≤ d)
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
    (hfe : HasFiniteEnergyMerge μ) (L : ℕ)
    (hforest : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc61_CoarseForestLeafCount ω L R)
    (hcoarseRoute : 0 < μ {ω | numInfiniteClusters d ω = ⊤} →
      ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site d,
        0 < μ (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃)) :
    μ {ω | numInfiniteClusters d ω = ⊤} = 0 :=
  bc61_infiniteClusters_top_null_of_coarse μ L (fun R => boxSV_boundaryCard d R)
    
    (fun R => bc62_coarse_expectation μ hinv L R)
    
    (fun ω R => bc61_coarseTcount_le_boundary_of_forest ω L R (hforest ω R))
    
    (fun R => bkc_boxFinsetBK_card_pos d R)
    
    (bkc_boundary_vol_tendsto d hd)
    
    (bc62_coarseTrifExistence_of_route μ hfe L hcoarseRoute)

end StatMech.Walls
