import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Lattice.SegmentDownClose.Part2
open Set SimpleGraph Function StatMech StatMech.Lattice


/--
[sdc_down_on_support_of_notInterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/SegmentDownClose.lean)
-/
@[path]
private lemma sdc_down_on_support_of_notInterior_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y : ℤ}
-- given
  (hz : (![x, y] : Site 2) ∈ jil_offSupportInterior Vc)
  (hnot : (![x, y - 1] : Site 2) ∉ jil_offSupportInterior Vc) :
-- imply
  (![x, y - 1] : Site 2) ∈ Vc.support := by
-- proof
  apply StatMech.Lattice.sdc_down_on_support_of_notInterior Vc hz hnot

/--
[sdc_no_segmentDown_of_bottomInterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/SegmentDownClose.lean)
-/
@[path]
private lemma sdc_no_segmentDown_of_bottomInterior_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y : ℤ}
-- given
  (hz : (![x, y] : Site 2) ∈ jil_offSupportInterior Vc)
  (hbot : ∀ t : ℤ, (![t, y - 1] : Site 2) ∉ jil_offSupportInterior Vc) :
-- imply
  ¬ ∃ cx : ℤ, x ≤ cx ∧ (∀ t : ℤ, x ≤ t → t ≤ cx → (![t, y] : Site 2) ∉ Vc.support) ∧ (![cx, y - 1] : Site 2) ∉ Vc.support := by
-- proof
  apply StatMech.Lattice.sdc_no_segmentDown_of_bottomInterior Vc hz hbot

/--
[sdc_fjord_raycount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/SegmentDownClose.lean)
-/
@[path]
private lemma sdc_fjord_raycount_eq
  {z : Site 2} :
-- imply
  jec_rayCount z sdc_fjord = (if 3 ≤ z 0 - 1 ∧ 0 ≤ z 1 - 1 ∧ z 1 - 1 ≤ 0 + (3:ℤ) - 1 then 1 else 0) + (if 4 ≤ z 0 - 1 ∧ 0 ≤ z 1 - 1 ∧ z 1 - 1 ≤ 0 + (3:ℤ) - 1 then 1 else 0) + (if 7 ≤ z 0 - 1 ∧ 0 ≤ z 1 - 1 ∧ z 1 - 1 ≤ 0 + (4:ℤ) - 1 then 1 else 0) + (if 0 ≤ z 0 - 1 ∧ 0 ≤ z 1 - 1 ∧ z 1 - 1 ≤ 0 + (4:ℤ) - 1 then 1 else 0) := by
-- proof
  apply StatMech.Lattice.sdc_fjord_raycount z

/--
[sdc_hsegRight_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/SegmentDownClose.lean)
-/
@[path]
private lemma sdc_hsegRight_mem_eq
  {row : ℤ} :
-- imply
  ∀ (k j : ℕ), ∀ (t : ℤ), j ≤ k → (![t + (j:ℤ), row] : Site 2) ∈ (jec_hsegRight row t k).support := by
-- proof
  apply StatMech.Lattice.sdc_hsegRight_mem row

/--
[sdc_vsegUp_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/SegmentDownClose.lean)
-/
@[path]
private lemma sdc_vsegUp_mem_eq
  {col : ℤ} :
-- imply
  ∀ (k j : ℕ), ∀ (r : ℤ), j ≤ k → (![col, r + (j:ℤ)] : Site 2) ∈ (jec_vsegUp col r k).support := by
-- proof
  apply StatMech.Lattice.sdc_vsegUp_mem col

/--
[sdc_hsegRight_mem'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/SegmentDownClose.lean)
-/
@[path]
private lemma sdc_hsegRight_mem'_eq
  {row t : ℤ}
  {k : ℕ}
  {c : ℤ}
-- given
  (h0 : t ≤ c)
  (h1 : c ≤ t + (k:ℤ)) :
-- imply
  (![c, row] : Site 2) ∈ (jec_hsegRight row t k).support := by
-- proof
  apply StatMech.Lattice.sdc_hsegRight_mem' row t k c h0 h1

/--
[sdc_vsegUp_mem'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/SegmentDownClose.lean)
-/
@[path]
private lemma sdc_vsegUp_mem'_eq
  {col r : ℤ}
  {k : ℕ}
  {c : ℤ}
-- given
  (h0 : r ≤ c)
  (h1 : c ≤ r + (k:ℤ)) :
-- imply
  (![col, c] : Site 2) ∈ (jec_vsegUp col r k).support := by
-- proof
  apply StatMech.Lattice.sdc_vsegUp_mem' col r k c h0 h1

/--
[sdc_fjord_support_locus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/SegmentDownClose.lean)
-/
@[path]
private lemma sdc_fjord_support_locus_eq
  {p : Site 2}
-- given
  (hp : p ∈ sdc_fjord.support) :
-- imply
  (p 1 = 0 ∧ 0 ≤ p 0 ∧ p 0 ≤ 3) ∨ (p 0 = 3 ∧ 0 ≤ p 1 ∧ p 1 ≤ 3) ∨ (p 1 = 3 ∧ 3 ≤ p 0 ∧ p 0 ≤ 4) ∨ (p 0 = 4 ∧ 0 ≤ p 1 ∧ p 1 ≤ 3) ∨ (p 1 = 0 ∧ 4 ≤ p 0 ∧ p 0 ≤ 7) ∨ (p 0 = 7 ∧ 0 ≤ p 1 ∧ p 1 ≤ 4) ∨ (p 1 = 4 ∧ 0 ≤ p 0 ∧ p 0 ≤ 7) ∨ (p 0 = 0 ∧ 0 ≤ p 1 ∧ p 1 ≤ 4) := by
-- proof
  apply StatMech.Lattice.sdc_fjord_support_locus p hp

/--
[sdc_fjord_off_51](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/SegmentDownClose.lean)
-/
@[path]
private lemma sdc_fjord_off_51_eq :
-- imply
  (![5, 1] : Site 2) ∉ sdc_fjord.support := by
-- proof
  apply StatMech.Lattice.sdc_fjord_off_51

/--
[sdc_fjord_off_61](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/SegmentDownClose.lean)
-/
@[path]
private lemma sdc_fjord_off_61_eq :
-- imply
  (![6, 1] : Site 2) ∉ sdc_fjord.support := by
-- proof
  apply StatMech.Lattice.sdc_fjord_off_61

/--
[sdc_fjord_off_11](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/SegmentDownClose.lean)
-/
@[path]
private lemma sdc_fjord_off_11_eq :
-- imply
  (![1, 1] : Site 2) ∉ sdc_fjord.support := by
-- proof
  apply StatMech.Lattice.sdc_fjord_off_11

/--
[sdc_fjord_on_41](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/SegmentDownClose.lean)
-/
@[path]
private lemma sdc_fjord_on_41_eq :
-- imply
  (![4, 1] : Site 2) ∈ sdc_fjord.support := by
-- proof
  apply StatMech.Lattice.sdc_fjord_on_41

/--
[sdc_fjord_on_50](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/SegmentDownClose.lean)
-/
@[path]
private lemma sdc_fjord_on_50_eq :
-- imply
  (![5, 0] : Site 2) ∈ sdc_fjord.support := by
-- proof
  apply StatMech.Lattice.sdc_fjord_on_50

/--
[sdc_fjord_on_60](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/SegmentDownClose.lean)
-/
@[path]
private lemma sdc_fjord_on_60_eq :
-- imply
  (![6, 0] : Site 2) ∈ sdc_fjord.support := by
-- proof
  apply StatMech.Lattice.sdc_fjord_on_60

/--
[sdc_fjord_on_71](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/SegmentDownClose.lean)
-/
@[path]
private lemma sdc_fjord_on_71_eq :
-- imply
  (![7, 1] : Site 2) ∈ sdc_fjord.support := by
-- proof
  apply StatMech.Lattice.sdc_fjord_on_71

/--
[sdc_fjord_interior_51](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/SegmentDownClose.lean)
-/
@[path]
private lemma sdc_fjord_interior_51_eq :
-- imply
  (![5, 1] : Site 2) ∈ jec_leftRegion sdc_fjord := by
-- proof
  apply StatMech.Lattice.sdc_fjord_interior_51

/--
[sdc_fjord_interior_11](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/SegmentDownClose.lean)
-/
@[path]
private lemma sdc_fjord_interior_11_eq :
-- imply
  (![1, 1] : Site 2) ∈ jec_leftRegion sdc_fjord := by
-- proof
  apply StatMech.Lattice.sdc_fjord_interior_11

/--
[sdc_fjord_mem_interior_51](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/SegmentDownClose.lean)
-/
@[path]
private lemma sdc_fjord_mem_interior_51_eq :
-- imply
  (![5, 1] : Site 2) ∈ jil_offSupportInterior sdc_fjord := by
-- proof
  apply StatMech.Lattice.sdc_fjord_mem_interior_51

/--
[sdc_fjord_mem_interior_11](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/SegmentDownClose.lean)
-/
@[path]
private lemma sdc_fjord_mem_interior_11_eq :
-- imply
  (![1, 1] : Site 2) ∈ jil_offSupportInterior sdc_fjord := by
-- proof
  apply StatMech.Lattice.sdc_fjord_mem_interior_11

/--
[sdc_fjord_body_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/SegmentDownClose.lean)
-/
@[path]
private lemma sdc_fjord_body_false_eq :
-- imply
  ¬ ∃ cx : ℤ, (5 : ℤ) ≤ cx ∧ (∀ t : ℤ, (5 : ℤ) ≤ t → t ≤ cx → (![t, 1] : Site 2) ∉ sdc_fjord.support) ∧ (![cx, 1 - 1] : Site 2) ∉ sdc_fjord.support := by
-- proof
  apply StatMech.Lattice.sdc_fjord_body_false

/--
[sdc_segmentDown_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/SegmentDownClose.lean)
-/
@[path]
private lemma sdc_segmentDown_false_eq :
-- imply
  ∃ (seed : Site 2), seed ∈ jil_offSupportInterior sdc_fjord ∧ ¬ rlc_SegmentDown sdc_fjord seed := by
-- proof
  apply StatMech.Lattice.sdc_segmentDown_false

/--
[sdc_forall_segmentDown_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/SegmentDownClose.lean)
-/
@[path]
private lemma sdc_forall_segmentDown_false_eq :
-- imply
  ¬ ∀ seed : Site 2, rlc_SegmentDown sdc_fjord seed := by
-- proof
  apply StatMech.Lattice.sdc_forall_segmentDown_false


-- created on 2026-10-23
