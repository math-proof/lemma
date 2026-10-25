import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Lattice.KingSegmentDownClose
open Set SimpleGraph Function StatMech StatMech.Lattice


/--
[ksd_stair_raycount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingSegmentDownClose.lean)
-/
@[path]
private lemma ksd_stair_raycount_eq
  {z : Site 2} :
-- imply
  jec_rayCount z ksd_stair = (if 2 ≤ z 0 - 1 ∧ 0 ≤ z 1 - 1 ∧ z 1 - 1 ≤ 0 + (1:ℤ) - 1 then 1 else 0) + (if 3 ≤ z 0 - 1 ∧ 1 ≤ z 1 - 1 ∧ z 1 - 1 ≤ 1 + (2:ℤ) - 1 then 1 else 0) + (if 1 ≤ z 0 - 1 ∧ 2 ≤ z 1 - 1 ∧ z 1 - 1 ≤ 2 + (1:ℤ) - 1 then 1 else 0) + (if 0 ≤ z 0 - 1 ∧ 0 ≤ z 1 - 1 ∧ z 1 - 1 ≤ 0 + (2:ℤ) - 1 then 1 else 0) := by
-- proof
  apply StatMech.Lattice.ksd_stair_raycount z

/--
[ksd_stair_support_locus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingSegmentDownClose.lean)
-/
@[path]
private lemma ksd_stair_support_locus_eq
  {p : Site 2}
-- given
  (hp : p ∈ ksd_stair.support) :
-- imply
  (p 1 = 0 ∧ 0 ≤ p 0 ∧ p 0 ≤ 2) ∨ (p 0 = 2 ∧ 0 ≤ p 1 ∧ p 1 ≤ 1) ∨ (p 1 = 1 ∧ 2 ≤ p 0 ∧ p 0 ≤ 3) ∨ (p 0 = 3 ∧ 1 ≤ p 1 ∧ p 1 ≤ 3) ∨ (p 1 = 3 ∧ 1 ≤ p 0 ∧ p 0 ≤ 3) ∨ (p 0 = 1 ∧ 2 ≤ p 1 ∧ p 1 ≤ 3) ∨ (p 1 = 2 ∧ 0 ≤ p 0 ∧ p 0 ≤ 1) ∨ (p 0 = 0 ∧ 0 ≤ p 1 ∧ p 1 ≤ 2) := by
-- proof
  apply StatMech.Lattice.ksd_stair_support_locus p hp

/--
[ksd_off_11](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingSegmentDownClose.lean)
-/
@[path]
private lemma ksd_off_11_eq :
-- imply
  (![1, 1] : Site 2) ∉ ksd_stair.support := by
-- proof
  apply StatMech.Lattice.ksd_off_11

/--
[ksd_off_22](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingSegmentDownClose.lean)
-/
@[path]
private lemma ksd_off_22_eq :
-- imply
  (![2, 2] : Site 2) ∉ ksd_stair.support := by
-- proof
  apply StatMech.Lattice.ksd_off_22

/--
[ksd_on_12](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingSegmentDownClose.lean)
-/
@[path]
private lemma ksd_on_12_eq :
-- imply
  (![1, 2] : Site 2) ∈ ksd_stair.support := by
-- proof
  apply StatMech.Lattice.ksd_on_12

/--
[ksd_on_21](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingSegmentDownClose.lean)
-/
@[path]
private lemma ksd_on_21_eq :
-- imply
  (![2, 1] : Site 2) ∈ ksd_stair.support := by
-- proof
  apply StatMech.Lattice.ksd_on_21

/--
[ksd_on_32](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingSegmentDownClose.lean)
-/
@[path]
private lemma ksd_on_32_eq :
-- imply
  (![3, 2] : Site 2) ∈ ksd_stair.support := by
-- proof
  apply StatMech.Lattice.ksd_on_32

/--
[ksd_hsegRight_edge_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingSegmentDownClose.lean)
-/
@[path]
private lemma ksd_hsegRight_edge_mem_eq
  {row : ℤ} :
-- imply
  ∀ (k j : ℕ), ∀ (t : ℤ), j < k → s((![t + (j:ℤ), row] : Site 2), (![t + (j:ℤ) + 1, row] : Site 2)) ∈ (jec_hsegRight row t k).edges := by
-- proof
  apply StatMech.Lattice.ksd_hsegRight_edge_mem row

/--
[ksd_vsegUp_edge_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingSegmentDownClose.lean)
-/
@[path]
private lemma ksd_vsegUp_edge_mem_eq
  {col : ℤ} :
-- imply
  ∀ (k j : ℕ), ∀ (r : ℤ), j < k → s((![col, r + (j:ℤ)] : Site 2), (![col, r + (j:ℤ) + 1] : Site 2)) ∈ (jec_vsegUp col r k).edges := by
-- proof
  apply StatMech.Lattice.ksd_vsegUp_edge_mem col

/--
[ksd_hsegRight_edge_mem'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingSegmentDownClose.lean)
-/
@[path]
private lemma ksd_hsegRight_edge_mem'_eq
  {row t : ℤ}
  {k : ℕ}
  {c : ℤ}
-- given
  (h0 : t ≤ c)
  (h1 : c < t + (k:ℤ)) :
-- imply
  s((![c, row] : Site 2), (![c + 1, row] : Site 2)) ∈ (jec_hsegRight row t k).edges := by
-- proof
  apply StatMech.Lattice.ksd_hsegRight_edge_mem' row t k c h0 h1

/--
[ksd_vsegUp_edge_mem'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingSegmentDownClose.lean)
-/
@[path]
private lemma ksd_vsegUp_edge_mem'_eq
  {col r : ℤ}
  {k : ℕ}
  {c : ℤ}
-- given
  (h0 : r ≤ c)
  (h1 : c < r + (k:ℤ)) :
-- imply
  s((![col, c] : Site 2), (![col, c + 1] : Site 2)) ∈ (jec_vsegUp col r k).edges := by
-- proof
  apply StatMech.Lattice.ksd_vsegUp_edge_mem' col r k c h0 h1

/--
[ksd_interior_11](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingSegmentDownClose.lean)
-/
@[path]
private lemma ksd_interior_11_eq :
-- imply
  (![1, 1] : Site 2) ∈ jec_leftRegion ksd_stair := by
-- proof
  apply StatMech.Lattice.ksd_interior_11

/--
[ksd_interior_22](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingSegmentDownClose.lean)
-/
@[path]
private lemma ksd_interior_22_eq :
-- imply
  (![2, 2] : Site 2) ∈ jec_leftRegion ksd_stair := by
-- proof
  apply StatMech.Lattice.ksd_interior_22

/--
[ksd_mem_interior_11](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingSegmentDownClose.lean)
-/
@[path]
private lemma ksd_mem_interior_11_eq :
-- imply
  (![1, 1] : Site 2) ∈ jil_offSupportInterior ksd_stair := by
-- proof
  apply StatMech.Lattice.ksd_mem_interior_11

/--
[ksd_mem_interior_22](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingSegmentDownClose.lean)
-/
@[path]
private lemma ksd_mem_interior_22_eq :
-- imply
  (![2, 2] : Site 2) ∈ jil_offSupportInterior ksd_stair := by
-- proof
  apply StatMech.Lattice.ksd_mem_interior_22

/--
[ksd_on_23](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingSegmentDownClose.lean)
-/
@[path]
private lemma ksd_on_23_eq :
-- imply
  (![2, 3] : Site 2) ∈ ksd_stair.support := by
-- proof
  apply StatMech.Lattice.ksd_on_23

/--
[ksd_on_33](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingSegmentDownClose.lean)
-/
@[path]
private lemma ksd_on_33_eq :
-- imply
  (![3, 3] : Site 2) ∈ ksd_stair.support := by
-- proof
  apply StatMech.Lattice.ksd_on_33

/--
[ksd_interior_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingSegmentDownClose.lean)
-/
@[path]
private lemma ksd_interior_eq_eq :
-- imply
  jil_offSupportInterior ksd_stair = {(![1, 1] : Site 2), (![2, 2] : Site 2)} := by
-- proof
  apply StatMech.Lattice.ksd_interior_eq

/--
[ksd_support_cells](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingSegmentDownClose.lean)
-/
@[path]
private lemma ksd_support_cells_eq
  {p : Site 2}
-- given
  (hp : p ∈ ksd_stair.support) :
-- imply
  p = (![0,0]:Site 2) ∨ p = (![1,0]:Site 2) ∨ p = (![2,0]:Site 2) ∨ p = (![2,1]:Site 2) ∨ p = (![3,1]:Site 2) ∨ p = (![3,2]:Site 2) ∨ p = (![3,3]:Site 2) ∨ p = (![2,3]:Site 2) ∨ p = (![1,3]:Site 2) ∨ p = (![1,2]:Site 2) ∨ p = (![0,2]:Site 2) ∨ p = (![0,1]:Site 2) := by
-- proof
  apply StatMech.Lattice.ksd_support_cells p hp

/--
[ksd_stair_fourThin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingSegmentDownClose.lean)
-/
@[path]
private lemma ksd_stair_fourThin_eq :
-- imply
  mci_FourThin ksd_stair := by
-- proof
  apply StatMech.Lattice.ksd_stair_fourThin

/--
[ksd_seed_is_11](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingSegmentDownClose.lean)
-/
@[path]
private lemma ksd_seed_is_11_eq
  {M : ℤ}
  {seed : Site 2}
-- given
  (hMb : ∀ z ∈ jec_leftRegion ksd_stair, (-M < z 0 ∧ z 0 ≤ M) ∧ (-M < z 1 ∧ z 1 ≤ M))
  (hseed : seed ∈ jil_offSupportInterior ksd_stair)
  (hmin : ∀ z ∈ jil_offSupportInterior ksd_stair, rlc_lexMeasure M seed ≤ rlc_lexMeasure M z) :
-- imply
  seed = (![1, 1] : Site 2) := by
-- proof
  apply StatMech.Lattice.ksd_seed_is_11 hMb hseed hmin

/--
[ksd_stair_body_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingSegmentDownClose.lean)
-/
@[path]
private lemma ksd_stair_body_false_eq :
-- imply
  ¬ ∃ cx : ℤ, (2 : ℤ) ≤ cx ∧ (∀ t : ℤ, (2 : ℤ) ≤ t → t ≤ cx → (![t, 2] : Site 2) ∉ ksd_stair.support) ∧ ((![cx, 2 - 1] : Site 2) ∉ ksd_stair.support ∨ ((![cx + 1, 2] : Site 2) ∉ ksd_stair.support ∧ (![cx + 1, 2 - 1] : Site 2) ∉ ksd_stair.support)) := by
-- proof
  apply StatMech.Lattice.ksd_stair_body_false

/--
[ksd_kingSegmentDown_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingSegmentDownClose.lean)
-/
@[path]
private lemma ksd_kingSegmentDown_false_eq :
-- imply
  ¬ kif_KingSegmentDown ksd_stair (![1, 1] : Site 2) := by
-- proof
  apply StatMech.Lattice.ksd_kingSegmentDown_false

/--
[ksd_kingSegmentDown_lexMinSeed_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingSegmentDownClose.lean)
-/
@[path]
private lemma ksd_kingSegmentDown_lexMinSeed_false_eq :
-- imply
  ∃ seed : Site 2, seed ∈ jil_offSupportInterior ksd_stair ∧ ¬ kif_KingSegmentDown ksd_stair seed := by
-- proof
  apply StatMech.Lattice.ksd_kingSegmentDown_lexMinSeed_false

/--
[ksd_kingRowLinked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingSegmentDownClose.lean)
-/
@[path]
private lemma ksd_kingRowLinked_eq :
-- imply
  mci_KingRowLinked ksd_stair (![1, 1] : Site 2) := by
-- proof
  apply StatMech.Lattice.ksd_kingRowLinked

/--
[ksd_residue_false_but_theorem_true](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingSegmentDownClose.lean)
-/
@[path]
private lemma ksd_residue_false_but_theorem_true_eq :
-- imply
  mci_FourThin ksd_stair ∧ mci_KingRowLinked ksd_stair (![1, 1] : Site 2) ∧ ¬ kif_KingSegmentDown ksd_stair (![1, 1] : Site 2) := by
-- proof
  apply StatMech.Lattice.ksd_residue_false_but_theorem_true


-- created on 2026-10-23
