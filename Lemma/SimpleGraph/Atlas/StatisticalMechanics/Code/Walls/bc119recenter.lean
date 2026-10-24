import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.bc119recenter
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc119_shell_of_walk_into_box_y](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc119recenter.lean)
-/
@[path]
private lemma bc119_shell_of_walk_into_box_y_eq
  {d : ℕ}
  {L : ℕ}
  {y : Site 2}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {b u x : Site 2}
  {w : (openSubgraph 2 ω).Walk u x} :
-- imply
  Connected 2 (removeSites (bc61_boxAround 2 L y) ω) b u → u ∉ bc61_boxAround 2 L y → x ∈ bc61_boxAround 2 L y → ∃ s t : Site 2, (openSubgraph 2 ω).Adj s t ∧ t ∈ bc61_boxAround 2 L y ∧ Connected 2 (removeSites (bc61_boxAround 2 L y) ω) b s := by
-- proof
  apply StatMech.Walls.bc119_shell_of_walk_into_box_y w

/--
[bc119_attach_of_meetsBox_y](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc119recenter.lean)
-/
@[path]
private lemma bc119_attach_of_meetsBox_y_eq
  {d : ℕ}
  {L : ℕ}
  {y : Site 2}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {x x' : Site 2}
-- given
  (hinf : (cluster 2 ω x).Infinite)
  (hx'box : x' ∈ bc61_boxAround 2 L y)
  (hxx' : cluster 2 ω x = cluster 2 ω x') :
-- imply
  ∃ a : Site 2, (∃ bx ∈ bc61_boxAround 2 L y, (openSubgraph 2 ω).Adj bx a) ∧ (cluster 2 (removeSites (bc61_boxAround 2 L y) ω) a).Infinite ∧ cluster 2 ω x = cluster 2 ω a := by
-- proof
  apply StatMech.Walls.bc119_attach_of_meetsBox_y hinf hx'box hxx'

/--
[bc119_merge_at_y](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc119recenter.lean)
-/
@[path]
private lemma bc119_merge_at_y_eq
  {d : ℕ}
  {L : ℕ}
  {y : Site 2}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {x₁ x₂ x₃ : Site 2}
-- given
  (hi₁ : (cluster 2 ω x₁).Infinite)
  (hi₂ : (cluster 2 ω x₂).Infinite)
  (hi₃ : (cluster 2 ω x₃).Infinite)
  (hd₁₂ : cluster 2 ω x₁ ≠ cluster 2 ω x₂)
  (hd₁₃ : cluster 2 ω x₁ ≠ cluster 2 ω x₃)
  (hd₂₃ : cluster 2 ω x₂ ≠ cluster 2 ω x₃)
  (hm₁ : ∃ x₁' ∈ bc61_boxAround 2 L y, cluster 2 ω x₁ = cluster 2 ω x₁')
  (hm₂ : ∃ x₂' ∈ bc61_boxAround 2 L y, cluster 2 ω x₂ = cluster 2 ω x₂')
  (hm₃ : ∃ x₃' ∈ bc61_boxAround 2 L y, cluster 2 ω x₃ = cluster 2 ω x₃') :
-- imply
  bc61_IsCoarseTrifurcation ω L y := by
-- proof
  apply StatMech.Walls.bc119_merge_at_y hi₁ hi₂ hi₃ hd₁₂ hd₁₃ hd₂₃ hm₁ hm₂ hm₃

/--
[bc119_merge_recentered](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc119recenter.lean)
-/
@[path]
private lemma bc119_merge_recentered_eq
  {d : ℕ}
  {L : ℕ}
  {y : Site 2}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {x₁ x₂ x₃ : Site 2}
-- given
  (hi₁ : (cluster 2 ω x₁).Infinite)
  (hi₂ : (cluster 2 ω x₂).Infinite)
  (hi₃ : (cluster 2 ω x₃).Infinite)
  (hd₁₂ : cluster 2 ω x₁ ≠ cluster 2 ω x₂)
  (hd₁₃ : cluster 2 ω x₁ ≠ cluster 2 ω x₃)
  (hd₂₃ : cluster 2 ω x₂ ≠ cluster 2 ω x₃)
  (hb₁ : x₁ ∈ bc61_boxAround 2 L y)
  (hb₂ : x₂ ∈ bc61_boxAround 2 L y)
  (hb₃ : x₃ ∈ bc61_boxAround 2 L y) :
-- imply
  bc61_IsCoarseTrifurcation ω L y := by
-- proof
  apply StatMech.Walls.bc119_merge_recentered hi₁ hi₂ hi₃ hd₁₂ hd₁₃ hd₂₃ hb₁ hb₂ hb₃

/--
[bc119_commonBox_of_close](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc119recenter.lean)
-/
@[path]
private lemma bc119_commonBox_of_close_eq
  {d : ℕ}
  {L : ℕ}
  {x₁ x₂ x₃ : Site 2}
-- given
  (h₂ : ∀ i, (x₂ i - x₁ i).natAbs ≤ L)
  (h₃ : ∀ i, (x₃ i - x₁ i).natAbs ≤ L) :
-- imply
  x₁ ∈ bc61_boxAround 2 L x₁ ∧ x₂ ∈ bc61_boxAround 2 L x₁ ∧ x₃ ∈ bc61_boxAround 2 L x₁ := by
-- proof
  apply StatMech.Walls.bc119_commonBox_of_close h₂ h₃

/--
[bc119_merge_recentered_of_close](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc119recenter.lean)
-/
@[path]
private lemma bc119_merge_recentered_of_close_eq
  {d : ℕ}
  {L : ℕ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {x₁ x₂ x₃ : Site 2}
-- given
  (hi₁ : (cluster 2 ω x₁).Infinite)
  (hi₂ : (cluster 2 ω x₂).Infinite)
  (hi₃ : (cluster 2 ω x₃).Infinite)
  (hd₁₂ : cluster 2 ω x₁ ≠ cluster 2 ω x₂)
  (hd₁₃ : cluster 2 ω x₁ ≠ cluster 2 ω x₃)
  (hd₂₃ : cluster 2 ω x₂ ≠ cluster 2 ω x₃)
  (h₂ : ∀ i, (x₂ i - x₁ i).natAbs ≤ L)
  (h₃ : ∀ i, (x₃ i - x₁ i).natAbs ≤ L) :
-- imply
  bc61_IsCoarseTrifurcation ω L x₁ := by
-- proof
  apply StatMech.Walls.bc119_merge_recentered_of_close hi₁ hi₂ hi₃ hd₁₂ hd₁₃ hd₂₃ h₂ h₃

/--
[bc119_originCoarseTrif_of_yCoarseTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc119recenter.lean)
-/
@[path]
private lemma bc119_originCoarseTrif_of_yCoarseTrif_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  {L : ℕ}
  {y : Site d}
-- given
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
  (hy : 0 < μ {ω | bc61_IsCoarseTrifurcation ω L y}) :
-- imply
  0 < μ {ω | bc61_IsCoarseTrifurcation ω L 0} := by
-- proof
  apply StatMech.Walls.bc119_originCoarseTrif_of_yCoarseTrif μ hinv L hy

/--
[bc119_coarseTrifExistence_of_recentered](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc119recenter.lean)
-/
@[path]
private lemma bc119_coarseTrifExistence_of_recentered_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  {L : ℕ}
-- given
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
  (hrec : 0 < μ {ω | numInfiniteClusters d ω = ⊤} → ∃ y : Site d, 0 < μ {ω | bc61_IsCoarseTrifurcation ω L y}) :
-- imply
  bc61_CoarseTrifExistence μ L := by
-- proof
  apply StatMech.Walls.bc119_coarseTrifExistence_of_recentered μ hinv L hrec

/--
[bc119_recenterBoxRoute_of_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc119recenter.lean)
-/
@[path]
private lemma bc119_recenterBoxRoute_of_residue_eq
  {d : ℕ}
  {L n : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (hres : bc119_RecenterBoxMerge d L n)
  (hω : ω ∈ threeMeetBox d n) :
-- imply
  ∃ (y : Site d) (W : Finset (Sym2 (Site d))), bc61_IsCoarseTrifurcation (forceOpenFinset W ω) L y := by
-- proof
  apply StatMech.Walls.bc119_recenterBoxRoute_of_residue hres hω

/--
[bc119_coarseTrifCover_of_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc119recenter.lean)
-/
@[path]
private lemma bc119_coarseTrifCover_of_residue_eq
  {d : ℕ}
  {L n : ℕ}
-- given
  (hres : bc119_RecenterBoxMerge d L n) :
-- imply
  threeMeetBox d n ⊆ ⋃ (y : Site d) (W : Finset (Sym2 (Site d))), (fun ω => forceOpenFinset W ω) ⁻¹' {ω | bc61_IsCoarseTrifurcation ω L y} := by
-- proof
  apply StatMech.Walls.bc119_coarseTrifCover_of_residue hres

/--
[bc119_originCoarseTrif_at_of_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc119recenter.lean)
-/
@[path]
private lemma bc119_originCoarseTrif_at_of_residue_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {L n : ℕ}
-- given
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
  (hfe : HasFiniteEnergyMerge μ)
  (hres : bc119_RecenterBoxMerge d L n)
  (hpos : 0 < μ (threeMeetBox d n)) :
-- imply
  0 < μ {ω | bc61_IsCoarseTrifurcation ω L 0} := by
-- proof
  apply StatMech.Walls.bc119_originCoarseTrif_at_of_residue μ hinv hfe hres hpos

/--
[bc119_coarseTrifExistence_of_recenterResidue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc119recenter.lean)
-/
@[path]
private lemma bc119_coarseTrifExistence_of_recenterResidue_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {L : ℕ}
-- given
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
  (hfe : HasFiniteEnergyMerge μ)
  (hres : ∀ n : ℕ, bc119_RecenterBoxMerge d L n) :
-- imply
  bc61_CoarseTrifExistence μ L := by
-- proof
  apply StatMech.Walls.bc119_coarseTrifExistence_of_recenterResidue μ hinv hfe L hres

/--
[bc119_recenterBoxMerge_of_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc119recenter.lean)
-/
@[path]
private lemma bc119_recenterBoxMerge_of_origin_eq
  {d : ℕ}
  {L n : ℕ}
-- given
  (hmerge : bc115_CoarseTrifMerge d L n) :
-- imply
  bc119_RecenterBoxMerge d L n := by
-- proof
  apply StatMech.Walls.bc119_recenterBoxMerge_of_origin hmerge

/--
[bc119_recenter_upperLines_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc119recenter.lean)
-/
@[path]
private lemma bc119_recenter_upperLines_witness_eq
  {d : ℕ}
  {L : ℕ}
-- given
  (hL : 3 ≤ L) :
-- imply
  ∃ (y : Site 2) (W : Finset (Sym2 (Site 2))), bc61_IsCoarseTrifurcation (forceOpenFinset W bc60_upperLines) L y := by
-- proof
  apply StatMech.Walls.bc119_recenter_upperLines_witness hL

/--
[bc119_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc119recenter.lean)
-/
@[path]
private lemma bc119_status_eq
  {d : ℕ} :
-- imply
  (∀ {L : ℕ} {y : Site 2} {ω : ConfigSpace (Sym2 (Site 2))} {x x' : Site 2}, (cluster 2 ω x).Infinite → x' ∈ bc61_boxAround 2 L y → cluster 2 ω x = cluster 2 ω x' → ∃ a : Site 2, (∃ bx ∈ bc61_boxAround 2 L y, (openSubgraph 2 ω).Adj bx a) ∧ (cluster 2 (removeSites (bc61_boxAround 2 L y) ω) a).Infinite ∧ cluster 2 ω x = cluster 2 ω a) ∧ (∀ (μ : Measure (ConfigSpace (Sym2 (Site d)))), IsTranslationInvariant (G := Multiplicative (Site d)) μ → ∀ (L : ℕ) (y : Site d), 0 < μ {ω | bc61_IsCoarseTrifurcation ω L y} → 0 < μ {ω | bc61_IsCoarseTrifurcation ω L 0}) ∧ (∀ (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ], IsTranslationInvariant (G := Multiplicative (Site d)) μ → HasFiniteEnergyMerge μ → ∀ (L : ℕ), (∀ n : ℕ, bc119_RecenterBoxMerge d L n) → bc61_CoarseTrifExistence μ L) ∧ (∀ (L n : ℕ), bc115_CoarseTrifMerge d L n → bc119_RecenterBoxMerge d L n) ∧ (∀ {L : ℕ}, 3 ≤ L → ∃ (y : Site 2) (W : Finset (Sym2 (Site 2))), bc61_IsCoarseTrifurcation (forceOpenFinset W bc60_upperLines) L y) := by
-- proof
  apply StatMech.Walls.bc119_status


-- created on 2026-10-23
