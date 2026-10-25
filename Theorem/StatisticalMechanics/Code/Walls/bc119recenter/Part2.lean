/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc119recenter.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc117mergeproof.Part3
import Def.StatisticalMechanics.Code.Walls.bc119recenter
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


theorem bc119_recenterBoxRoute_of_residue {L n : ℕ} (hres : bc119_RecenterBoxMerge d L n)
    {ω : ConfigSpace (Sym2 (Site d))} (hω : ω ∈ threeMeetBox d n) :
    ∃ (y : Site d) (W : Finset (Sym2 (Site d))),
      bc61_IsCoarseTrifurcation (forceOpenFinset W ω) L y := by
  obtain ⟨x₁, x₂, x₃, ⟨hb1, hb2, hb3⟩, ⟨hi1, hi2, hi3⟩, hd12, hd13, hd23⟩ :=
    tfe_three_distinct_infinite_of_box hω
  exact hres ω hω x₁ x₂ x₃ hb1 hb2 hb3 hi1 hi2 hi3 hd12 hd13 hd23


theorem bc119_coarseTrifCover_of_residue {L n : ℕ} (hres : bc119_RecenterBoxMerge d L n) :
    threeMeetBox d n ⊆
      ⋃ (y : Site d) (W : Finset (Sym2 (Site d))),
        (fun ω => forceOpenFinset W ω) ⁻¹' {ω | bc61_IsCoarseTrifurcation ω L y} := by
  intro ω hω
  obtain ⟨y, W, htrif⟩ := bc119_recenterBoxRoute_of_residue hres hω
  simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_setOf_eq]
  exact ⟨y, W, htrif⟩


theorem bc119_originCoarseTrif_at_of_residue
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
    (hfe : HasFiniteEnergyMerge μ) {L n : ℕ} (hres : bc119_RecenterBoxMerge d L n)
    (hpos : 0 < μ (threeMeetBox d n)) :
    0 < μ {ω | bc61_IsCoarseTrifurcation ω L 0} := by
  classical
  set ι := Site d × Finset (Sym2 (Site d)) with hι
  set B : ι → Set (ConfigSpace (Sym2 (Site d))) :=
    fun p => (fun ω => forceOpenFinset p.2 ω) ⁻¹' {ω | bc61_IsCoarseTrifurcation ω L p.1} with hB
  have hcover : threeMeetBox d n ⊆ ⋃ p : ι, B p := by
    intro ω hω
    obtain ⟨y, W, htrif⟩ := bc119_recenterBoxRoute_of_residue hres hω
    exact Set.mem_iUnion.mpr ⟨(y, W), by simpa [hB, Set.mem_preimage] using htrif⟩
  obtain ⟨p, hppos⟩ := DisjointPaths.exists_pos_of_cover μ hcover hpos
  obtain ⟨y, W⟩ := p
  have hy : 0 < μ {ω | bc61_IsCoarseTrifurcation ω L y} :=
    DisjointPaths.pos_of_forceOpen_preimage μ hfe W (bc62_measurableSet_coarseTrif L y) subset_rfl hppos
  exact bc119_originCoarseTrif_of_yCoarseTrif μ hinv L hy


theorem bc119_coarseTrifExistence_of_recenterResidue
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
    (hfe : HasFiniteEnergyMerge μ) (L : ℕ) (hres : ∀ n : ℕ, bc119_RecenterBoxMerge d L n) :
    bc61_CoarseTrifExistence μ L := by
  intro htop
  obtain ⟨n, hnpos⟩ := exists_threeMeetBox_pos μ htop
  exact bc119_originCoarseTrif_at_of_residue μ hinv hfe (hres n) hnpos


theorem bc119_recenterBoxMerge_of_origin {L n : ℕ}
    (hmerge : bc115_CoarseTrifMerge d L n) : bc119_RecenterBoxMerge d L n := by
  intro ω hω x₁ x₂ x₃ hb₁ hb₂ hb₃ hi₁ hi₂ hi₃ hd₁₂ hd₁₃ hd₂₃
  obtain ⟨W, htrif⟩ := hmerge ω hω x₁ x₂ x₃ hb₁ hb₂ hb₃ hi₁ hi₂ hi₃ hd₁₂ hd₁₃ hd₂₃
  exact ⟨0, W, htrif⟩


theorem bc119_recenter_upperLines_witness {L : ℕ} (hL : 3 ≤ L) :
    ∃ (y : Site 2) (W : Finset (Sym2 (Site 2))),
      bc61_IsCoarseTrifurcation (forceOpenFinset W bc60_upperLines) L y := by
  refine ⟨0, ∅, ?_⟩
  rw [bc115_forceOpen_empty]
  exact bc61_wholeBox_severs_upperLines hL


theorem bc119_status :
    
    (∀ {L : ℕ} {y : Site 2} {ω : ConfigSpace (Sym2 (Site 2))} {x x' : Site 2},
      (cluster 2 ω x).Infinite → x' ∈ bc61_boxAround 2 L y → cluster 2 ω x = cluster 2 ω x' →
      ∃ a : Site 2,
        (∃ bx ∈ bc61_boxAround 2 L y, (openSubgraph 2 ω).Adj bx a) ∧
        (cluster 2 (removeSites (bc61_boxAround 2 L y) ω) a).Infinite ∧
        cluster 2 ω x = cluster 2 ω a) ∧
    
    (∀ (μ : Measure (ConfigSpace (Sym2 (Site d)))),
      IsTranslationInvariant (G := Multiplicative (Site d)) μ → ∀ (L : ℕ) (y : Site d),
      0 < μ {ω | bc61_IsCoarseTrifurcation ω L y} → 0 < μ {ω | bc61_IsCoarseTrifurcation ω L 0}) ∧
    
    (∀ (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ],
      IsTranslationInvariant (G := Multiplicative (Site d)) μ → HasFiniteEnergyMerge μ →
      ∀ (L : ℕ), (∀ n : ℕ, bc119_RecenterBoxMerge d L n) → bc61_CoarseTrifExistence μ L) ∧
    
    (∀ (L n : ℕ), bc115_CoarseTrifMerge d L n → bc119_RecenterBoxMerge d L n) ∧
    
    (∀ {L : ℕ}, 3 ≤ L →
      ∃ (y : Site 2) (W : Finset (Sym2 (Site 2))),
        bc61_IsCoarseTrifurcation (forceOpenFinset W bc60_upperLines) L y) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro L y ω x x' hinf hx'box hxx'; exact bc119_attach_of_meetsBox_y hinf hx'box hxx'
  · intro μ hinv L y hy; exact bc119_originCoarseTrif_of_yCoarseTrif μ hinv L hy
  · intro μ _ hinv hfe L hres; exact bc119_coarseTrifExistence_of_recenterResidue μ hinv hfe L hres
  · intro L n hmerge; exact bc119_recenterBoxMerge_of_origin hmerge
  · intro L hL; exact bc119_recenter_upperLines_witness hL

end StatMech.Walls
