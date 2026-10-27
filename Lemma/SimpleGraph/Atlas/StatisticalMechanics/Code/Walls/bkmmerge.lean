import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bkmmerge
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bkm_box_subset_boxAround](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkmmerge.lean)
-/
@[path]
private lemma bkm_box_subset_boxAround_eq
  {d : ℕ}
  {L n : ℕ}
  {x : Site 2}
-- given
  (hnL : n ≤ L)
  (hx : x ∈ box 2 n) :
-- imply
  x ∈ bc61_boxAround 2 L 0 := by
-- proof
  apply StatMech.Walls.bkm_box_subset_boxAround hnL hx

/--
[bkm_coarseTrif_of_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkmmerge.lean)
-/
@[path]
private lemma bkm_coarseTrif_of_le_eq
  {d : ℕ}
  {L n : ℕ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {x₁ x₂ x₃ : Site 2}
-- given
  (hnL : n ≤ L)
  (hb₁ : x₁ ∈ box 2 n)
  (hb₂ : x₂ ∈ box 2 n)
  (hb₃ : x₃ ∈ box 2 n)
  (hi₁ : (cluster 2 ω x₁).Infinite)
  (hi₂ : (cluster 2 ω x₂).Infinite)
  (hi₃ : (cluster 2 ω x₃).Infinite)
  (hd₁₂ : cluster 2 ω x₁ ≠ cluster 2 ω x₂)
  (hd₁₃ : cluster 2 ω x₁ ≠ cluster 2 ω x₃)
  (hd₂₃ : cluster 2 ω x₂ ≠ cluster 2 ω x₃) :
-- imply
  bc61_IsCoarseTrifurcation ω L 0 := by
-- proof
  apply StatMech.Walls.bkm_coarseTrif_of_le hnL hb₁ hb₂ hb₃ hi₁ hi₂ hi₃ hd₁₂ hd₁₃ hd₂₃

/--
[bkm_recenterBoxMerge_of_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkmmerge.lean)
-/
@[path]
private lemma bkm_recenterBoxMerge_of_le_eq
  {d : ℕ}
  {L n : ℕ}
-- given
  (hnL : n ≤ L) :
-- imply
  bc119_RecenterBoxMerge 2 L n := by
-- proof
  apply StatMech.Walls.bkm_recenterBoxMerge_of_le hnL

/--
[bkm_recenterBoxMerge_diag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkmmerge.lean)
-/
@[path]
private lemma bkm_recenterBoxMerge_diag_eq
  {d : ℕ}
  {n : ℕ} :
-- imply
  bc119_RecenterBoxMerge 2 n n := by
-- proof
  apply StatMech.Walls.bkm_recenterBoxMerge_diag n

/--
[bkm_coarseTrifExistence_diag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkmmerge.lean)
-/
@[path]
private lemma bkm_coarseTrifExistence_diag_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site 2)))}
  [IsProbabilityMeasure μ]
-- given
  (hinv : IsTranslationInvariant (G := Multiplicative (Site 2)) μ)
  (hfe : HasFiniteEnergyMerge μ)
  (htop : 0 < μ {ω | numInfiniteClusters 2 ω = ⊤}) :
-- imply
  ∃ L : ℕ, 0 < μ {ω | bc61_IsCoarseTrifurcation ω L 0} := by
-- proof
  apply StatMech.Walls.bkm_coarseTrifExistence_diag μ hinv hfe htop

/--
[bkm_coarseTrifExistence_atSomeScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkmmerge.lean)
-/
@[path]
private lemma bkm_coarseTrifExistence_atSomeScale_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site 2)))}
  [IsProbabilityMeasure μ]
-- given
  (hinv : IsTranslationInvariant (G := Multiplicative (Site 2)) μ)
  (hfe : HasFiniteEnergyMerge μ)
  (htop : 0 < μ {ω | numInfiniteClusters 2 ω = ⊤}) :
-- imply
  ∃ L : ℕ, bc61_CoarseTrifExistence μ L := by
-- proof
  apply StatMech.Walls.bkm_coarseTrifExistence_atSomeScale μ hinv hfe htop

/--
[bkm_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkmmerge.lean)
-/
@[path]
private lemma bkm_status_eq
  {d : ℕ} :
-- imply
  (∀ (L n : ℕ), n ≤ L → bc119_RecenterBoxMerge 2 L n) ∧ (∀ (n : ℕ), bc119_RecenterBoxMerge 2 n n) ∧ (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ], IsTranslationInvariant (G := Multiplicative (Site 2)) μ → HasFiniteEnergyMerge μ → 0 < μ {ω | numInfiniteClusters 2 ω = ⊤} → ∃ L : ℕ, bc61_CoarseTrifExistence μ L) := by
-- proof
  apply StatMech.Walls.bkm_status


-- created on 2026-10-23
