/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/HrouteDisjointPaths.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationConstruction.Part3
import Abbrev.StatisticalMechanics.Code.Percolation.HrouteDisjointPaths
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

namespace DisjointPaths

variable {d : ℕ}


theorem corridorWorks_of_corridors (ω : ConfigSpace (Sym2 (Site d)))
    (a₁ a₂ a₃ : Site d) (G : Finset (Sym2 (Site d)))
    (hne : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃)
    (hadj : (hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧
      (hypercubicLattice d).Adj 0 a₃)
    (w₁ w₂ w₃ : Site d)
    (hcor₁ : Relation.ReflTransGen (CorridorStep G) a₁ w₁)
    (hcor₂ : Relation.ReflTransGen (CorridorStep G) a₂ w₂)
    (hcor₃ : Relation.ReflTransGen (CorridorStep G) a₃ w₃)
    (hw₁ : (cluster d (removeSite 0 (forceOpenFinset G ω)) w₁).Infinite)
    (hw₂ : (cluster d (removeSite 0 (forceOpenFinset G ω)) w₂).Infinite)
    (hw₃ : (cluster d (removeSite 0 (forceOpenFinset G ω)) w₃).Infinite)
    (S₁ S₂ S₃ : Set (Site d))
    (hmem₁ : a₁ ∈ S₁) (hmem₂ : a₂ ∈ S₂) (hmem₃ : a₃ ∈ S₃)
    (hcl₁ : ∀ u v, u ∈ S₁ →
      (openSubgraph d (removeSite 0 (forceOpenFinset G ω))).Adj u v → v ∈ S₁)
    (hcl₂ : ∀ u v, u ∈ S₂ →
      (openSubgraph d (removeSite 0 (forceOpenFinset G ω))).Adj u v → v ∈ S₂)
    (hcl₃ : ∀ u v, u ∈ S₃ →
      (openSubgraph d (removeSite 0 (forceOpenFinset G ω))).Adj u v → v ∈ S₃)
    (hd12 : Disjoint S₁ S₂) (hd13 : Disjoint S₁ S₃) (hd23 : Disjoint S₂ S₃) :
    ω ∈ CorridorWorks a₁ a₂ a₃ G := by
  have hinf₁ : (cluster d (removeSite 0 (forceOpenFinset G ω)) a₁).Infinite := by
    rw [cluster_eq_of_connected (connected_removeSite_forceOpen_of_corridor ω G hcor₁)]; exact hw₁
  have hinf₂ : (cluster d (removeSite 0 (forceOpenFinset G ω)) a₂).Infinite := by
    rw [cluster_eq_of_connected (connected_removeSite_forceOpen_of_corridor ω G hcor₂)]; exact hw₂
  have hinf₃ : (cluster d (removeSite 0 (forceOpenFinset G ω)) a₃).Infinite := by
    rw [cluster_eq_of_connected (connected_removeSite_forceOpen_of_corridor ω G hcor₃)]; exact hw₃
  exact corridorWorks_of_separated ω a₁ a₂ a₃ G hne hadj S₁ S₂ S₃ hmem₁ hmem₂ hmem₃
    hcl₁ hcl₂ hcl₃ hd12 hd13 hd23 ⟨hinf₁, hinf₂, hinf₃⟩


theorem measurableSet_clusterInfinite_removeSite (x a : Site d) :
    MeasurableSet
      {ω : ConfigSpace (Sym2 (Site d)) | (cluster d (removeSite x ω) a).Infinite} := by
  have h : {ω : ConfigSpace (Sym2 (Site d)) | (cluster d (removeSite x ω) a).Infinite}
      = (fun ω => removeSite x ω) ⁻¹' {ω' | (cluster d ω' a).Infinite} := rfl
  rw [h]
  exact (measurable_removeSite x) (measurableSet_clusterInfinite a)


theorem measurableSet_neighborTrifPrecursor (a₁ a₂ a₃ : Site d) :
    MeasurableSet (NeighborTrifPrecursor d a₁ a₂ a₃) := by
  classical
  have heq : NeighborTrifPrecursor d a₁ a₂ a₃
      = (if (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧
            ((hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧
              (hypercubicLattice d).Adj 0 a₃) then Set.univ else ∅)
        ∩ ({ω | (cluster d (removeSite 0 ω) a₁).Infinite}
            ∩ {ω | (cluster d (removeSite 0 ω) a₂).Infinite}
            ∩ {ω | (cluster d (removeSite 0 ω) a₃).Infinite})
        ∩ ({ω | ¬ Connected d (removeSite 0 ω) a₁ a₂}
            ∩ {ω | ¬ Connected d (removeSite 0 ω) a₁ a₃}
            ∩ {ω | ¬ Connected d (removeSite 0 ω) a₂ a₃}) := by
    ext ω
    simp only [NeighborTrifPrecursor, Set.mem_setOf_eq, Set.mem_inter_iff]
    by_cases hh : (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧
        ((hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧
          (hypercubicLattice d).Adj 0 a₃)
    · simp only [if_pos hh, Set.mem_univ, true_and]
      constructor
      · rintro ⟨_, _, ⟨hi1, hi2, hi3⟩, ⟨hs1, hs2, hs3⟩⟩
        exact ⟨⟨⟨hi1, hi2⟩, hi3⟩, ⟨⟨hs1, hs2⟩, hs3⟩⟩
      · rintro ⟨⟨⟨hi1, hi2⟩, hi3⟩, ⟨⟨hs1, hs2⟩, hs3⟩⟩
        exact ⟨hh.1, hh.2, ⟨hi1, hi2, hi3⟩, ⟨hs1, hs2, hs3⟩⟩
    · simp only [if_neg hh, Set.mem_empty_iff_false, false_and, iff_false]
      rintro ⟨hne, hadj, _, _⟩
      exact hh ⟨hne, hadj⟩
  rw [heq]
  refine MeasurableSet.inter (MeasurableSet.inter ?_ ?_) ?_
  · by_cases hh : (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧
        ((hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧
          (hypercubicLattice d).Adj 0 a₃)
    · rw [if_pos hh]; exact MeasurableSet.univ
    · rw [if_neg hh]; exact MeasurableSet.empty
  · exact ((measurableSet_clusterInfinite_removeSite 0 a₁).inter
      (measurableSet_clusterInfinite_removeSite 0 a₂)).inter
      (measurableSet_clusterInfinite_removeSite 0 a₃)
  · exact (((measurableSet_connected_removeSite 0 a₁ a₂).compl).inter
      ((measurableSet_connected_removeSite 0 a₁ a₃).compl)).inter
      ((measurableSet_connected_removeSite 0 a₂ a₃).compl)


theorem exists_pos_of_cover {ι : Type*} [Countable ι]
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    {A : Set (ConfigSpace (Sym2 (Site d)))} {B : ι → Set (ConfigSpace (Sym2 (Site d)))}
    (hsub : A ⊆ ⋃ i, B i) (hApos : 0 < μ A) : ∃ i, 0 < μ (B i) := by
  by_contra hcon
  simp only [not_exists, not_lt, nonpos_iff_eq_zero] at hcon
  have hunion0 : μ (⋃ i, B i) = 0 := by
    refine le_antisymm ?_ bot_le
    have hsum : μ (⋃ i, B i) ≤ ∑' i, μ (B i) := measure_iUnion_le B
    have hz : ∑' i, μ (B i) = 0 := by simp [hcon]
    rw [hz] at hsum; exact hsum
  have hle : μ A ≤ μ (⋃ i, B i) := measure_mono hsub
  rw [hunion0] at hle
  exact absurd (le_antisymm hle bot_le) (ne_of_gt hApos)


theorem pos_of_forceOpen_preimage
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hfe : HasFiniteEnergyMerge μ) (G : Finset (Sym2 (Site d)))
    {A B : Set (ConfigSpace (Sym2 (Site d)))} (hmB : MeasurableSet B)
    (hsub : A ⊆ (fun ω => forceOpenFinset G ω) ⁻¹' B) (hApos : 0 < μ A) :
    0 < μ B := by
  by_contra h
  rw [not_lt, nonpos_iff_eq_zero] at h
  have hac := hfe G
  have hpush : (μ.map (fun ω => forceOpenFinset G ω)) B
      = μ ((fun ω => forceOpenFinset G ω) ⁻¹' B) :=
    Measure.map_apply (measurable_forceOpenFinset G) hmB
  have hpre0 : μ ((fun ω => forceOpenFinset G ω) ⁻¹' B) = 0 := by rw [← hpush]; exact hac h
  have hle : μ A ≤ μ ((fun ω => forceOpenFinset G ω) ⁻¹' B) := measure_mono hsub
  rw [hpre0] at hle
  exact absurd (le_antisymm hle bot_le) (ne_of_gt hApos)


theorem hroute_at_of_corridorCover
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hfe : HasFiniteEnergyMerge μ) {n : ℕ}
    (hcorr : threeMeetBox d n ⊆
      ⋃ (a₁ : Site d) (a₂ : Site d) (a₃ : Site d) (G : Finset (Sym2 (Site d))),
        CorridorWorks a₁ a₂ a₃ G)
    (hpos : 0 < μ (threeMeetBox d n)) :
    ∃ a₁ a₂ a₃ : Site d, 0 < μ (NeighborTrifPrecursor d a₁ a₂ a₃) := by
  classical
  
  set ι := Site d × Site d × Site d × Finset (Sym2 (Site d)) with hι
  set B : ι → Set (ConfigSpace (Sym2 (Site d))) :=
    fun p => CorridorWorks p.1 p.2.1 p.2.2.1 p.2.2.2 with hB
  have hcover : threeMeetBox d n ⊆ ⋃ p : ι, B p := by
    intro ω hω
    obtain ⟨a₁, a₂, a₃, G, hmem⟩ := by
      have := hcorr hω
      simpa only [Set.mem_iUnion] using this
    exact Set.mem_iUnion.mpr ⟨(a₁, a₂, a₃, G), hmem⟩
  
  obtain ⟨p, hppos⟩ := exists_pos_of_cover μ hcover hpos
  obtain ⟨a₁, a₂, a₃, G⟩ := p
  
  refine ⟨a₁, a₂, a₃, ?_⟩
  exact pos_of_forceOpen_preimage μ hfe G
    (measurableSet_neighborTrifPrecursor a₁ a₂ a₃)
    (corridorWorks_subset_force_precursor a₁ a₂ a₃ G) hppos


theorem hroute_of_corridorCover
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hfe : HasFiniteEnergyMerge μ)
    (hcorr : ∀ n : ℕ, threeMeetBox d n ⊆
      ⋃ (a₁ : Site d) (a₂ : Site d) (a₃ : Site d) (G : Finset (Sym2 (Site d))),
        CorridorWorks a₁ a₂ a₃ G) :
    ∀ n : ℕ, 0 < μ (threeMeetBox d n) →
      ∃ a₁ a₂ a₃ : Site d, 0 < μ (NeighborTrifPrecursor d a₁ a₂ a₃) :=
  fun n hpos => hroute_at_of_corridorCover μ hfe (hcorr n) hpos


end DisjointPaths
end Percolation
end StatMech
