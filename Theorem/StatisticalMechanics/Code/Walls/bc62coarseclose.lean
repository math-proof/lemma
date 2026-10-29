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
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc62_boxAround_shift (g : Multiplicative (Site d)) (L : ℕ) (y : Site d) :
    bc61_boxAround d L (g • y) = (bc61_boxAround d L y).image (fun z => g • z) := by
  classical
  ext x
  rw [bc61_mem_boxAround, Finset.mem_image]
  constructor
  · intro hx
    refine ⟨g⁻¹ • x, ?_, by rw [smul_inv_smul]⟩
    rw [bc61_mem_boxAround]
    
    have hcoord : ∀ i : Fin d, ((g⁻¹ • x) - y) i = (x - g • y) i := by
      intro i
      simp only [Pi.sub_apply, smul_site_apply, toAdd_inv, Pi.neg_apply]; ring
    rw [mem_box] at hx ⊢
    intro i; rw [hcoord i]; exact hx i
  · rintro ⟨z, hz, rfl⟩
    rw [bc61_mem_boxAround] at hz
    have hcoord : ∀ i : Fin d, ((g • z) - (g • y)) i = (z - y) i := by
      intro i
      simp only [Pi.sub_apply, smul_site_apply]; ring
    rw [mem_box] at hz ⊢
    intro i; rw [hcoord i]; exact hz i


theorem bc62_removeSites_shift (g : Multiplicative (Site d)) (T : Finset (Site d))
    (ω : ConfigSpace (Sym2 (Site d))) :
    removeSites (T.image (fun z => g • z)) (shift g ω) = shift g (removeSites T ω) := by
  classical
  funext e
  simp only [removeSites, shift_apply]
  
  have hguard : (∃ t ∈ T.image (fun z => g • z), t ∈ e) ↔ (∃ t ∈ T, t ∈ g⁻¹ • e) := by
    constructor
    · rintro ⟨t, ht, hte⟩
      rw [Finset.mem_image] at ht
      obtain ⟨s, hs, rfl⟩ := ht
      refine ⟨s, hs, ?_⟩
      
      have : g⁻¹ • (g • s) ∈ g⁻¹ • e := Sym2.mem_map.mpr ⟨g • s, hte, rfl⟩
      rwa [inv_smul_smul] at this
    · rintro ⟨t, ht, hte⟩
      refine ⟨g • t, Finset.mem_image.mpr ⟨t, ht, rfl⟩, ?_⟩
      
      have : g • t ∈ g • (g⁻¹ • e) := Sym2.mem_map.mpr ⟨t, hte, rfl⟩
      rwa [smul_inv_smul] at this
  by_cases h : ∃ t ∈ T.image (fun z => g • z), t ∈ e
  · rw [if_pos h, if_pos (hguard.mp h)]
  · rw [if_neg h, if_neg (fun hc => h (hguard.mpr hc))]


theorem bc62_removeBox_shift (g : Multiplicative (Site d)) (L : ℕ) (y : Site d)
    (ω : ConfigSpace (Sym2 (Site d))) :
    removeSites (bc61_boxAround d L (g • y)) (shift g ω)
      = shift g (removeSites (bc61_boxAround d L y) ω) := by
  rw [bc62_boxAround_shift]; exact bc62_removeSites_shift g (bc61_boxAround d L y) ω


theorem bc62_isCoarseTrif_shift (g : Multiplicative (Site d))
    (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y : Site d) :
    bc61_IsCoarseTrifurcation (shift g ω) L (g • y) ↔ bc61_IsCoarseTrifurcation ω L y := by
  constructor
  · rintro ⟨a₁, a₂, a₃, hb1, hb2, hb3, hinf, hsep⟩
    refine ⟨g⁻¹ • a₁, g⁻¹ • a₂, g⁻¹ • a₃, ?_, ?_, ?_, ?_, ?_⟩
    
    · obtain ⟨b₁, hb1mem, hb1adj⟩ := hb1
      refine ⟨g⁻¹ • b₁, ?_, ?_⟩
      · rw [bc62_boxAround_shift] at hb1mem
        rw [Finset.mem_image] at hb1mem
        obtain ⟨s, hs, rfl⟩ := hb1mem; rwa [inv_smul_smul]
      · have := (openSubgraph_adj_shift g ω (g⁻¹ • b₁) (g⁻¹ • a₁)).mp
        simp only [smul_inv_smul] at this; exact this hb1adj
    · obtain ⟨b₂, hb2mem, hb2adj⟩ := hb2
      refine ⟨g⁻¹ • b₂, ?_, ?_⟩
      · rw [bc62_boxAround_shift] at hb2mem
        rw [Finset.mem_image] at hb2mem
        obtain ⟨s, hs, rfl⟩ := hb2mem; rwa [inv_smul_smul]
      · have := (openSubgraph_adj_shift g ω (g⁻¹ • b₂) (g⁻¹ • a₂)).mp
        simp only [smul_inv_smul] at this; exact this hb2adj
    · obtain ⟨b₃, hb3mem, hb3adj⟩ := hb3
      refine ⟨g⁻¹ • b₃, ?_, ?_⟩
      · rw [bc62_boxAround_shift] at hb3mem
        rw [Finset.mem_image] at hb3mem
        obtain ⟨s, hs, rfl⟩ := hb3mem; rwa [inv_smul_smul]
      · have := (openSubgraph_adj_shift g ω (g⁻¹ • b₃) (g⁻¹ • a₃)).mp
        simp only [smul_inv_smul] at this; exact this hb3adj
    
    · have hcl : ∀ a : Site d,
          cluster d (removeSites (bc61_boxAround d L (g • y)) (shift g ω)) (g • (g⁻¹ • a))
            = (fun z => g • z) '' (cluster d (removeSites (bc61_boxAround d L y) ω) (g⁻¹ • a)) := by
        intro a
        rw [bc62_removeBox_shift]; exact cluster_shift g (removeSites (bc61_boxAround d L y) ω) (g⁻¹ • a)
      refine ⟨?_, ?_, ?_⟩
      · have h := hinf.1; rw [show a₁ = g • (g⁻¹ • a₁) by rw [smul_inv_smul], hcl a₁] at h
        exact (Set.infinite_image_iff (Set.injOn_of_injective (smul_injective g))).mp h
      · have h := hinf.2.1; rw [show a₂ = g • (g⁻¹ • a₂) by rw [smul_inv_smul], hcl a₂] at h
        exact (Set.infinite_image_iff (Set.injOn_of_injective (smul_injective g))).mp h
      · have h := hinf.2.2; rw [show a₃ = g • (g⁻¹ • a₃) by rw [smul_inv_smul], hcl a₃] at h
        exact (Set.infinite_image_iff (Set.injOn_of_injective (smul_injective g))).mp h
    
    · refine ⟨?_, ?_, ?_⟩
      · intro hcon
        have : Connected d (shift g (removeSites (bc61_boxAround d L y) ω))
            (g • (g⁻¹ • a₁)) (g • (g⁻¹ • a₂)) :=
          (connected_shift g (removeSites (bc61_boxAround d L y) ω) (g⁻¹ • a₁) (g⁻¹ • a₂)).mpr hcon
        rw [smul_inv_smul, smul_inv_smul, ← bc62_removeBox_shift] at this
        exact hsep.1 this
      · intro hcon
        have : Connected d (shift g (removeSites (bc61_boxAround d L y) ω))
            (g • (g⁻¹ • a₁)) (g • (g⁻¹ • a₃)) :=
          (connected_shift g (removeSites (bc61_boxAround d L y) ω) (g⁻¹ • a₁) (g⁻¹ • a₃)).mpr hcon
        rw [smul_inv_smul, smul_inv_smul, ← bc62_removeBox_shift] at this
        exact hsep.2.1 this
      · intro hcon
        have : Connected d (shift g (removeSites (bc61_boxAround d L y) ω))
            (g • (g⁻¹ • a₂)) (g • (g⁻¹ • a₃)) :=
          (connected_shift g (removeSites (bc61_boxAround d L y) ω) (g⁻¹ • a₂) (g⁻¹ • a₃)).mpr hcon
        rw [smul_inv_smul, smul_inv_smul, ← bc62_removeBox_shift] at this
        exact hsep.2.2 this
  · rintro ⟨a₁, a₂, a₃, hb1, hb2, hb3, hinf, hsep⟩
    refine ⟨g • a₁, g • a₂, g • a₃, ?_, ?_, ?_, ?_, ?_⟩
    
    · obtain ⟨b₁, hb1mem, hb1adj⟩ := hb1
      refine ⟨g • b₁, ?_, (openSubgraph_adj_shift g ω b₁ a₁).mpr hb1adj⟩
      rw [bc62_boxAround_shift]; exact Finset.mem_image.mpr ⟨b₁, hb1mem, rfl⟩
    · obtain ⟨b₂, hb2mem, hb2adj⟩ := hb2
      refine ⟨g • b₂, ?_, (openSubgraph_adj_shift g ω b₂ a₂).mpr hb2adj⟩
      rw [bc62_boxAround_shift]; exact Finset.mem_image.mpr ⟨b₂, hb2mem, rfl⟩
    · obtain ⟨b₃, hb3mem, hb3adj⟩ := hb3
      refine ⟨g • b₃, ?_, (openSubgraph_adj_shift g ω b₃ a₃).mpr hb3adj⟩
      rw [bc62_boxAround_shift]; exact Finset.mem_image.mpr ⟨b₃, hb3mem, rfl⟩
    
    · have hcl : ∀ a : Site d,
          cluster d (removeSites (bc61_boxAround d L (g • y)) (shift g ω)) (g • a)
            = (fun z => g • z) '' (cluster d (removeSites (bc61_boxAround d L y) ω) a) := by
        intro a; rw [bc62_removeBox_shift]; exact cluster_shift g (removeSites (bc61_boxAround d L y) ω) a
      refine ⟨?_, ?_, ?_⟩
      · rw [hcl a₁]; exact (Set.infinite_image_iff (Set.injOn_of_injective (smul_injective g))).mpr hinf.1
      · rw [hcl a₂]; exact (Set.infinite_image_iff (Set.injOn_of_injective (smul_injective g))).mpr hinf.2.1
      · rw [hcl a₃]; exact (Set.infinite_image_iff (Set.injOn_of_injective (smul_injective g))).mpr hinf.2.2
    
    · rw [bc62_removeBox_shift]
      refine ⟨?_, ?_, ?_⟩
      · exact fun hcon => hsep.1 ((connected_shift g (removeSites (bc61_boxAround d L y) ω) a₁ a₂).mp hcon)
      · exact fun hcon => hsep.2.1 ((connected_shift g (removeSites (bc61_boxAround d L y) ω) a₁ a₃).mp hcon)
      · exact fun hcon => hsep.2.2 ((connected_shift g (removeSites (bc61_boxAround d L y) ω) a₂ a₃).mp hcon)


theorem bc62_measurable_removeSites (T : Finset (Site d)) :
    Measurable (fun ω : ConfigSpace (Sym2 (Site d)) => removeSites T ω) := by
  classical
  apply measurable_pi_lambda
  intro e
  unfold removeSites
  by_cases h : ∃ t ∈ T, t ∈ e
  · simp only [h, if_true]; exact measurable_const
  · simp only [h, if_false]; exact measurable_pi_apply e


theorem bc62_measurableSet_connected_removeSites (T : Finset (Site d)) (a b : Site d) :
    MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | Connected d (removeSites T ω) a b} := by
  have h : {ω : ConfigSpace (Sym2 (Site d)) | Connected d (removeSites T ω) a b}
      = (fun ω => removeSites T ω) ⁻¹' {ω' | Connected d ω' a b} := rfl
  rw [h]
  exact (bc62_measurable_removeSites T) (measurableSet_connected a b)


theorem bc62_measurableSet_clusterInfinite_removeSites (T : Finset (Site d)) (a : Site d) :
    MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | (cluster d (removeSites T ω) a).Infinite} := by
  have h : {ω : ConfigSpace (Sym2 (Site d)) | (cluster d (removeSites T ω) a).Infinite}
      = (fun ω => removeSites T ω) ⁻¹' {ω' | (cluster d ω' a).Infinite} := rfl
  rw [h]
  exact (bc62_measurable_removeSites T) (measurableSet_clusterInfinite a)


theorem bc62_measurableSet_boxAdjacent (L : ℕ) (y a : Site d) :
    MeasurableSet
      {ω : ConfigSpace (Sym2 (Site d)) | ∃ b ∈ bc61_boxAround d L y, (openSubgraph d ω).Adj b a} := by
  classical
  have heq : {ω : ConfigSpace (Sym2 (Site d)) | ∃ b ∈ bc61_boxAround d L y, (openSubgraph d ω).Adj b a}
      = ⋃ b ∈ bc61_boxAround d L y, {ω | (openSubgraph d ω).Adj b a} := by
    ext ω; simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
  rw [heq]
  exact MeasurableSet.biUnion (bc61_boxAround d L y).countable_toSet
    (fun b _ => measurableSet_openAdj b a)


theorem bc62_measurableSet_coarseTrif (L : ℕ) (y : Site d) :
    MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | bc61_IsCoarseTrifurcation ω L y} := by
  classical
  have heq : {ω : ConfigSpace (Sym2 (Site d)) | bc61_IsCoarseTrifurcation ω L y}
      = ⋃ a₁ : Site d, ⋃ a₂ : Site d, ⋃ a₃ : Site d,
          (({ω | ∃ b ∈ bc61_boxAround d L y, (openSubgraph d ω).Adj b a₁}
              ∩ {ω | ∃ b ∈ bc61_boxAround d L y, (openSubgraph d ω).Adj b a₂}
              ∩ {ω | ∃ b ∈ bc61_boxAround d L y, (openSubgraph d ω).Adj b a₃})
            ∩ ({ω | (cluster d (removeSites (bc61_boxAround d L y) ω) a₁).Infinite}
                ∩ {ω | (cluster d (removeSites (bc61_boxAround d L y) ω) a₂).Infinite}
                ∩ {ω | (cluster d (removeSites (bc61_boxAround d L y) ω) a₃).Infinite})
            ∩ ({ω | ¬ Connected d (removeSites (bc61_boxAround d L y) ω) a₁ a₂}
                ∩ {ω | ¬ Connected d (removeSites (bc61_boxAround d L y) ω) a₁ a₃}
                ∩ {ω | ¬ Connected d (removeSites (bc61_boxAround d L y) ω) a₂ a₃})) := by
    ext ω
    simp only [bc61_IsCoarseTrifurcation, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · rintro ⟨a₁, a₂, a₃, hb1, hb2, hb3, ⟨hi1, hi2, hi3⟩, ⟨hs1, hs2, hs3⟩⟩
      exact ⟨a₁, a₂, a₃, ⟨⟨⟨hb1, hb2⟩, hb3⟩, ⟨⟨hi1, hi2⟩, hi3⟩⟩, ⟨⟨hs1, hs2⟩, hs3⟩⟩
    · rintro ⟨a₁, a₂, a₃, ⟨⟨⟨hb1, hb2⟩, hb3⟩, ⟨⟨hi1, hi2⟩, hi3⟩⟩, ⟨⟨hs1, hs2⟩, hs3⟩⟩
      exact ⟨a₁, a₂, a₃, hb1, hb2, hb3, ⟨hi1, hi2, hi3⟩, ⟨hs1, hs2, hs3⟩⟩
  rw [heq]
  refine MeasurableSet.iUnion fun a₁ => MeasurableSet.iUnion fun a₂ =>
    MeasurableSet.iUnion fun a₃ => ?_
  refine MeasurableSet.inter (MeasurableSet.inter ?_ ?_) ?_
  · exact ((bc62_measurableSet_boxAdjacent L y a₁).inter
      (bc62_measurableSet_boxAdjacent L y a₂)).inter (bc62_measurableSet_boxAdjacent L y a₃)
  · exact ((bc62_measurableSet_clusterInfinite_removeSites (bc61_boxAround d L y) a₁).inter
      (bc62_measurableSet_clusterInfinite_removeSites (bc61_boxAround d L y) a₂)).inter
      (bc62_measurableSet_clusterInfinite_removeSites (bc61_boxAround d L y) a₃)
  · exact (((bc62_measurableSet_connected_removeSites (bc61_boxAround d L y) a₁ a₂).compl).inter
      ((bc62_measurableSet_connected_removeSites (bc61_boxAround d L y) a₁ a₃).compl)).inter
      ((bc62_measurableSet_connected_removeSites (bc61_boxAround d L y) a₂ a₃).compl)


theorem bc62_coarseTrifProb_const (μ : Measure (ConfigSpace (Sym2 (Site d))))
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ) (L : ℕ) (y : Site d) :
    μ {ω | bc61_IsCoarseTrifurcation ω L y} = μ {ω | bc61_IsCoarseTrifurcation ω L 0} := by
  set g : Multiplicative (Site d) := Multiplicative.ofAdd y with hg
  have hgy : g • (0 : Site d) = y := by
    change Multiplicative.toAdd g + (0 : Site d) = y
    simp [hg]
  have hpre : (shift g : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d))) ⁻¹'
      {ω | bc61_IsCoarseTrifurcation ω L y} = {ω | bc61_IsCoarseTrifurcation ω L 0} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    rw [← hgy, bc62_isCoarseTrif_shift g ω L 0]
  calc μ {ω | bc61_IsCoarseTrifurcation ω L y}
      = μ ((shift g) ⁻¹' {ω | bc61_IsCoarseTrifurcation ω L y}) :=
        (hinv.measure_preimage g (bc62_measurableSet_coarseTrif L y)).symm
    _ = μ {ω | bc61_IsCoarseTrifurcation ω L 0} := by rw [hpre]


theorem bc62_coarseTcount_eq_sum_indicator (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) :
    (bc61_coarseTcount ω L R : ENNReal) =
      ∑ y ∈ boxFinsetBK d R,
        ({ω' | bc61_IsCoarseTrifurcation ω' L y}.indicator (fun _ => (1 : ENNReal))) ω := by
  classical
  rw [bc61_coarseTcount, bc61_coarseTrifFinset, Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro y _
  by_cases h : bc61_IsCoarseTrifurcation ω L y
  · rw [if_pos h, Set.indicator_of_mem (show ω ∈ {ω' | bc61_IsCoarseTrifurcation ω' L y} from h)]
  · rw [if_neg h, Set.indicator_of_notMem (show ω ∉ {ω' | bc61_IsCoarseTrifurcation ω' L y} from h)]


theorem bc62_coarse_expectation (μ : Measure (ConfigSpace (Sym2 (Site d))))
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ) (L R : ℕ) :
    ((boxFinsetBK d R).card : ENNReal) * μ {ω | bc61_IsCoarseTrifurcation ω L 0}
      = ∫⁻ ω, (bc61_coarseTcount ω L R : ENNReal) ∂μ := by
  classical
  have hmeas : ∀ y : Site d, Measurable
      (fun ω => ({ω' | bc61_IsCoarseTrifurcation ω' L y}.indicator (fun _ => (1 : ENNReal))) ω) :=
    fun y => Measurable.indicator measurable_const (bc62_measurableSet_coarseTrif L y)
  calc ((boxFinsetBK d R).card : ENNReal) * μ {ω | bc61_IsCoarseTrifurcation ω L 0}
      = (boxFinsetBK d R).card • μ {ω | bc61_IsCoarseTrifurcation ω L 0} := by
        rw [nsmul_eq_mul]
    _ = ∑ _y ∈ boxFinsetBK d R, μ {ω | bc61_IsCoarseTrifurcation ω L 0} := by
        rw [Finset.sum_const]
    _ = ∑ y ∈ boxFinsetBK d R, μ {ω | bc61_IsCoarseTrifurcation ω L y} := by
        apply Finset.sum_congr rfl; intro y _; exact (bc62_coarseTrifProb_const μ hinv L y).symm
    _ = ∑ y ∈ boxFinsetBK d R,
          ∫⁻ ω, ({ω' | bc61_IsCoarseTrifurcation ω' L y}.indicator (fun _ => (1 : ENNReal))) ω ∂μ := by
        apply Finset.sum_congr rfl; intro y _
        rw [MeasureTheory.lintegral_indicator (bc62_measurableSet_coarseTrif L y)]; simp
    _ = ∫⁻ ω, ∑ y ∈ boxFinsetBK d R,
          ({ω' | bc61_IsCoarseTrifurcation ω' L y}.indicator (fun _ => (1 : ENNReal))) ω ∂μ := by
        rw [MeasureTheory.lintegral_finsetSum]; intro y _; exact hmeas y
    _ = ∫⁻ ω, (bc61_coarseTcount ω L R : ENNReal) ∂μ := by
        apply lintegral_congr; intro ω; exact (bc62_coarseTcount_eq_sum_indicator ω L R).symm


theorem bc62_removeSites_forceOpen_eq (T : Finset (Site d)) (F : Finset (Sym2 (Site d)))
    (hF : ∀ e ∈ F, ∃ t ∈ T, t ∈ e) (ω : ConfigSpace (Sym2 (Site d))) :
    removeSites T (forceOpenFinset F ω) = removeSites T ω := by
  classical
  funext e
  unfold removeSites forceOpenFinset
  by_cases hT : ∃ t ∈ T, t ∈ e
  · simp [hT]
  · simp only [hT, if_false]
    by_cases hef : e ∈ F
    · exact absurd (hF e hef) hT
    · simp [hef]


theorem bc62_isCoarseTrifurcation_of_neighbors
    (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ)
    (a₁ a₂ a₃ b₁ b₂ b₃ : Site d)
    (hb1 : b₁ ∈ bc61_boxAround d L 0) (hb2 : b₂ ∈ bc61_boxAround d L 0)
    (hb3 : b₃ ∈ bc61_boxAround d L 0)
    (hadj1 : (hypercubicLattice d).Adj b₁ a₁)
    (hadj2 : (hypercubicLattice d).Adj b₂ a₂)
    (hadj3 : (hypercubicLattice d).Adj b₃ a₃)
    (hinf1 : (cluster d (removeSites (bc61_boxAround d L 0) ω) a₁).Infinite)
    (hinf2 : (cluster d (removeSites (bc61_boxAround d L 0) ω) a₂).Infinite)
    (hinf3 : (cluster d (removeSites (bc61_boxAround d L 0) ω) a₃).Infinite)
    (hsep12 : ¬ Connected d (removeSites (bc61_boxAround d L 0) ω) a₁ a₂)
    (hsep13 : ¬ Connected d (removeSites (bc61_boxAround d L 0) ω) a₁ a₃)
    (hsep23 : ¬ Connected d (removeSites (bc61_boxAround d L 0) ω) a₂ a₃) :
    bc61_IsCoarseTrifurcation
      (forceOpenFinset {s(b₁, a₁), s(b₂, a₂), s(b₃, a₃)} ω) L 0 := by
  classical
  set T : Finset (Site d) := bc61_boxAround d L 0 with hT
  set F : Finset (Sym2 (Site d)) := {s(b₁, a₁), s(b₂, a₂), s(b₃, a₃)} with hFdef
  set ω' := forceOpenFinset F ω with hω'
  
  have hFmem : ∀ e ∈ F, ∃ t ∈ T, t ∈ e := by
    intro e he
    simp only [hFdef, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with h | h | h
    · exact ⟨b₁, hb1, by rw [h]; exact Sym2.mem_mk_left _ _⟩
    · exact ⟨b₂, hb2, by rw [h]; exact Sym2.mem_mk_left _ _⟩
    · exact ⟨b₃, hb3, by rw [h]; exact Sym2.mem_mk_left _ _⟩
  
  have hrm : removeSites T ω' = removeSites T ω := bc62_removeSites_forceOpen_eq T F hFmem ω
  
  have hopen1 : (openSubgraph d ω').Adj b₁ a₁ :=
    (openSubgraph_adj (d := d) (ω := ω') b₁ a₁).mpr ⟨hadj1, forceOpenFinset_of_mem (by simp [hFdef]) ω⟩
  have hopen2 : (openSubgraph d ω').Adj b₂ a₂ :=
    (openSubgraph_adj (d := d) (ω := ω') b₂ a₂).mpr ⟨hadj2, forceOpenFinset_of_mem (by simp [hFdef]) ω⟩
  have hopen3 : (openSubgraph d ω').Adj b₃ a₃ :=
    (openSubgraph_adj (d := d) (ω := ω') b₃ a₃).mpr ⟨hadj3, forceOpenFinset_of_mem (by simp [hFdef]) ω⟩
  
  refine ⟨a₁, a₂, a₃, ⟨b₁, hb1, hopen1⟩, ⟨b₂, hb2, hopen2⟩, ⟨b₃, hb3, hopen3⟩, ?_, ?_⟩
  · rw [hrm]; exact ⟨hinf1, hinf2, hinf3⟩
  · rw [hrm]; exact ⟨hsep12, hsep13, hsep23⟩


end StatMech.Walls
