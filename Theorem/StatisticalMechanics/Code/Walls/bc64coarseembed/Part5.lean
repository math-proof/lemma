/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc64coarseembed.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc63coarseforest.Part2
import Def.StatisticalMechanics.Code.Walls.bc64coarseembed.Part5
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


open Classical in


theorem bc64_coarseArmEmbedding_of_boundaryInjection (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {z₀ z₁ : Site d} (hz₀ : z₀ ∈ vertexBoundary d R) (hz₁ : z₁ ∈ vertexBoundary d R)
    (hzne : z₀ ≠ z₁) (hinj : bc64_CoarseBoundaryInjection ω L R) :
    bc63_CoarseArmEmbedding ω L R := by
  classical
  rw [bc63_coarseArmEmbedding_iff_forestLeafCount]
  set Tf := bc61_coarseTrifFinset ω L R with hTf
  rcases Finset.eq_empty_or_nonempty Tf with hemp | hne
  · 
    apply bc63_coarseForestLeafCount_of_noTrif ω L R hz₀ hz₁ hzne
    intro y hybox htri
    have hymem : y ∈ Tf := by rw [hTf, bc61_mem_coarseTrifFinset]; exact ⟨hybox, htri⟩
    rw [hemp] at hymem; exact absurd hymem (Finset.notMem_empty y)
  · 
    obtain ⟨lam, hlamB, hlamInj⟩ := hinj
    have hTfne : Nonempty (↑Tf : Type) := hne.to_subtype
    obtain ⟨t0, ht0⟩ := hne
    let W := (↑Tf : Type) × Fin 4
    let ιT : Site d → W := fun y =>
      if hy : y ∈ Tf then (⟨y, hy⟩, 0) else (⟨t0, ht0⟩, 0)
    refine ⟨W, inferInstance, ⟨(⟨t0, ht0⟩, 0)⟩, inferInstance, bc64_starForest (↑Tf : Type),
      inferInstance, ιT, lam, bc64_starForest_acyclic _, ?_, ?_, ?_, ?_, ?_⟩
    · 
      intro v; obtain ⟨t, i⟩ := v; exact bc64_starForest_min_degree (t, i)
    · 
      intro y hybox htri
      have hy : y ∈ Tf := by rw [hTf, bc61_mem_coarseTrifFinset]; exact ⟨hybox, htri⟩
      change 3 ≤ (bc64_starForest (↑Tf : Type)).degree (ιT y)
      have hιT : ιT y = (⟨y, hy⟩, (0 : Fin 4)) := dif_pos hy
      rw [hιT, bc64_starForest_degree, bc64_starG_centre_deg]
    · 
      intro y hybox htri z hzbox htriz hyz
      have hy : y ∈ Tf := by rw [hTf, bc61_mem_coarseTrifFinset]; exact ⟨hybox, htri⟩
      have hz : z ∈ Tf := by rw [hTf, bc61_mem_coarseTrifFinset]; exact ⟨hzbox, htriz⟩
      simp only [ιT, dif_pos hy, dif_pos hz] at hyz
      exact Subtype.ext_iff.mp (Prod.ext_iff.mp hyz).1
    · 
      intro v hv; obtain ⟨t, i⟩ := v
      rw [bc64_starForest_deg1_iff] at hv
      exact hlamB (t, i) hv
    · 
      intro u hu v hv huv
      rw [Finset.mem_coe, Finset.mem_filter] at hu hv
      obtain ⟨t1, i1⟩ := u; obtain ⟨t2, i2⟩ := v
      rw [bc64_starForest_deg1_iff] at hu hv
      exact hlamInj hu.2 hv.2 huv


theorem bc64_coarseTcount_le_boundary_of_boundaryInjection (ω : ConfigSpace (Sym2 (Site d)))
    (L R : ℕ) {z₀ z₁ : Site d} (hz₀ : z₀ ∈ vertexBoundary d R) (hz₁ : z₁ ∈ vertexBoundary d R)
    (hzne : z₀ ≠ z₁) (hinj : bc64_CoarseBoundaryInjection ω L R) :
    bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R :=
  bc63_coarseTcount_le_boundary_of_armEmbedding ω L R
    (bc64_coarseArmEmbedding_of_boundaryInjection ω L R hz₀ hz₁ hzne hinj)


theorem bc64_disjointBoxes_multiTrif (L : ℕ) :
    Disjoint (bc61_boxAround 2 L (0 : Site 2)) (bc61_boxAround 2 L (bc57_pt (2 * (L : ℤ) + 1) 0)) := by
  refine bc64_boxAround_disjoint_of_farCoord 0 ?_
  have hcoord : ((0 : Site 2) - bc57_pt (2 * (L : ℤ) + 1) 0) 0 = -(2 * (L : ℤ) + 1) := by
    simp only [Pi.sub_apply]; rw [bc57_pt_fst]; simp
  rw [hcoord, Int.natAbs_neg]
  have hval : (2 * (L : ℤ) + 1).natAbs = 2 * L + 1 := by
    have : (2 * (L : ℤ) + 1) = ((2 * L + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [this, Int.natAbs_natCast]
  omega


theorem bc64_disjointBoxes_sublattice (L : ℕ) {m m' : ℤ} (hmm : m ≠ m') :
    Disjoint (bc61_boxAround 2 L (bc57_pt ((2 * (L : ℤ) + 1) * m) 0))
      (bc61_boxAround 2 L (bc57_pt ((2 * (L : ℤ) + 1) * m') 0)) := by
  refine bc64_boxAround_disjoint_of_farCoord 0 ?_
  have hcoord : (bc57_pt ((2 * (L : ℤ) + 1) * m) 0 - bc57_pt ((2 * (L : ℤ) + 1) * m') 0) 0
      = (2 * (L : ℤ) + 1) * (m - m') := by
    simp only [Pi.sub_apply]; rw [bc57_pt_fst, bc57_pt_fst]; ring
  rw [hcoord]
  have hne : m - m' ≠ 0 := sub_ne_zero.mpr hmm
  have h1 : 1 ≤ (m - m').natAbs := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hne)
  have hfactor : (2 * (L : ℤ) + 1).natAbs = 2 * L + 1 := by
    have hcast : (2 * (L : ℤ) + 1) = ((2 * L + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [hcast, Int.natAbs_natCast]
  have habs : ((2 * (L : ℤ) + 1) * (m - m')).natAbs = (2 * L + 1) * (m - m').natAbs := by
    rw [Int.natAbs_mul, hfactor]
  rw [habs]; nlinarith [h1]


theorem bc64_line1_connected_right (a : ℤ) (j : ℕ) :
    Connected 2 bc60_upperLines (bc57_pt a 1) (bc57_pt (a + (j : ℤ)) 1) := by
  induction j with
  | zero => simpa using connected_refl _ (bc57_pt a 1)
  | succ i ih =>
    have hstep : Connected 2 bc60_upperLines (bc57_pt (a + (i : ℤ)) 1) (bc57_pt (a + (i : ℤ) + 1) 1) :=
      IsOpenEdge.connected ⟨bc57_pt_adj (a + (i : ℤ)) 1, bc60_open (a + (i : ℤ)) (by norm_num)⟩
    have hcast : a + ((i + 1 : ℕ) : ℤ) = a + (i : ℤ) + 1 := by push_cast; ring
    rw [hcast]; exact ih.trans hstep


theorem bc64_line1_connected (a b : ℤ) :
    Connected 2 bc60_upperLines (bc57_pt a 1) (bc57_pt b 1) := by
  rcases le_total a b with hab | hab
  · have hj : b = a + ((b - a).toNat : ℤ) := by rw [Int.toNat_of_nonneg (by omega)]; ring
    rw [hj]; exact bc64_line1_connected_right a (b - a).toNat
  · have hj : a = b + ((a - b).toNat : ℤ) := by rw [Int.toNat_of_nonneg (by omega)]; ring
    rw [hj]; exact (bc64_line1_connected_right b (a - b).toNat).symm


theorem bc64_arms_can_share_boundary (L : ℕ) :
    Disjoint (bc61_boxAround 2 L (0 : Site 2))
        (bc61_boxAround 2 L (bc57_pt (2 * (L : ℤ) + 1) 0)) ∧
      Connected 2 bc60_upperLines
        (bc57_pt ((L : ℤ) + 1) 1) (bc57_pt (2 * (L : ℤ) + 1 + ((L : ℤ) + 1)) 1) :=
  ⟨bc64_disjointBoxes_multiTrif L,
   bc64_line1_connected ((L : ℤ) + 1) (2 * (L : ℤ) + 1 + ((L : ℤ) + 1))⟩


theorem bc64_infiniteClusters_top_null_of_boundaryInjection_route
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ] (hd : 1 ≤ d)
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
    (hfe : HasFiniteEnergyMerge μ) (L : ℕ)
    (hbdvertices : ∀ R : ℕ, ∃ z₀ z₁ : Site d,
      z₀ ∈ vertexBoundary d R ∧ z₁ ∈ vertexBoundary d R ∧ z₀ ≠ z₁)
    (hbinj : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc64_CoarseBoundaryInjection ω L R)
    (hcoarseRoute : 0 < μ {ω | numInfiniteClusters d ω = ⊤} →
      ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site d,
        0 < μ (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃)) :
    μ {ω | numInfiniteClusters d ω = ⊤} = 0 := by
  refine bc63_infiniteClusters_top_null_of_armEmbedding_route μ hd hinv hfe L (fun ω R => ?_)
    hcoarseRoute
  obtain ⟨z₀, z₁, hz₀, hz₁, hzne⟩ := hbdvertices R
  exact bc64_coarseArmEmbedding_of_boundaryInjection ω L R hz₀ hz₁ hzne (hbinj ω R)


theorem bc64_status :
    
    (∀ {L : ℕ} {y y' : Site d}, (∃ i, 2 * L < ((y - y') i).natAbs) →
      Disjoint (bc61_boxAround d L y) (bc61_boxAround d L y')) ∧
    
    (∀ (β : Type), (bc64_starForest β).IsAcyclic) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (z₀ z₁ : Site d),
      z₀ ∈ vertexBoundary d R → z₁ ∈ vertexBoundary d R → z₀ ≠ z₁ →
      bc64_CoarseBoundaryInjection ω L R → bc63_CoarseArmEmbedding ω L R) ∧
    
    (∀ (L : ℕ),
      Disjoint (bc61_boxAround 2 L (0 : Site 2))
          (bc61_boxAround 2 L (bc57_pt (2 * (L : ℤ) + 1) 0)) ∧
        Connected 2 bc60_upperLines
          (bc57_pt ((L : ℤ) + 1) 1) (bc57_pt (2 * (L : ℤ) + 1 + ((L : ℤ) + 1)) 1)) :=
  ⟨fun hfar => bc64_boxAround_disjoint_of_far hfar,
   fun β => bc64_starForest_acyclic β,
   fun ω L R z₀ z₁ hz₀ hz₁ hzne hinj =>
     bc64_coarseArmEmbedding_of_boundaryInjection ω L R hz₀ hz₁ hzne hinj,
   fun L => bc64_arms_can_share_boundary L⟩

end StatMech.Walls
