import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc73seqcompress.Part3
open Finset StatMech StatMech.Walls


/--
[rc73_mem_slice0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc73seqcompress.lean)
-/
@[path]
private lemma rc73_mem_slice0_eq
  [DecidableEq α]
  {i : α}
  {𝒜 : Finset (Finset α)}
  {s : Finset α} :
-- imply
  s ∈ rc73_slice0 i 𝒜 ↔ s ∈ 𝒜 ∧ i ∉ s := by
-- proof
  apply StatMech.Walls.rc73_mem_slice0 i 𝒜 s

/--
[rc73_mem_slice1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc73seqcompress.lean)
-/
@[path]
private lemma rc73_mem_slice1_eq
  [DecidableEq α]
  {i : α}
  {𝒜 : Finset (Finset α)}
  {s : Finset α} :
-- imply
  s ∈ rc73_slice1 i 𝒜 ↔ insert i s ∈ 𝒜 ∧ i ∉ s := by
-- proof
  apply StatMech.Walls.rc73_mem_slice1 i 𝒜 s

/--
[rc73_slice1_notMem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc73seqcompress.lean)
-/
@[path]
private lemma rc73_slice1_notMem_eq
  [DecidableEq α]
  {i : α}
  {𝒜 : Finset (Finset α)}
  {s : Finset α}
-- given
  (hs : s ∈ rc73_slice1 i 𝒜) :
-- imply
  i ∉ s := by
-- proof
  apply StatMech.Walls.rc73_slice1_notMem i 𝒜 hs

/--
[rc73_slice0_notMem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc73seqcompress.lean)
-/
@[path]
private lemma rc73_slice0_notMem_eq
  [DecidableEq α]
  {i : α}
  {𝒜 : Finset (Finset α)}
  {s : Finset α}
-- given
  (hs : s ∈ rc73_slice0 i 𝒜) :
-- imply
  i ∉ s := by
-- proof
  apply StatMech.Walls.rc73_slice0_notMem i 𝒜 hs

/--
[rc73_card_present_eq_slice1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc73seqcompress.lean)
-/
@[path]
private lemma rc73_card_present_eq_slice1_eq
  [DecidableEq α]
  {i : α}
  {𝒜 : Finset (Finset α)} :
-- imply
  (𝒜.filter (fun s => i ∈ s)).card = (rc73_slice1 i 𝒜).card := by
-- proof
  apply StatMech.Walls.rc73_card_present_eq_slice1 i 𝒜

/--
[rc73_card_eq_slices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc73seqcompress.lean)
-/
@[path]
private lemma rc73_card_eq_slices_eq
  [DecidableEq α]
  {i : α}
  {𝒜 : Finset (Finset α)} :
-- imply
  𝒜.card = (rc73_slice0 i 𝒜).card + (rc73_slice1 i 𝒜).card := by
-- proof
  apply StatMech.Walls.rc73_card_eq_slices i 𝒜

/--
[rc73_upComp_parts_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc73seqcompress.lean)
-/
@[path]
private lemma rc73_upComp_parts_disjoint_eq
  [DecidableEq α]
  {i : α}
  {𝒜 : Finset (Finset α)} :
-- imply
  Disjoint (rc73_slice0 i 𝒜 ∩ rc73_slice1 i 𝒜) ((rc73_slice0 i 𝒜 ∪ rc73_slice1 i 𝒜).image (insert i)) := by
-- proof
  apply StatMech.Walls.rc73_upComp_parts_disjoint i 𝒜

/--
[rc73_card_high](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc73seqcompress.lean)
-/
@[path]
private lemma rc73_card_high_eq
  [DecidableEq α]
  {i : α}
  {𝒜 : Finset (Finset α)} :
-- imply
  ((rc73_slice0 i 𝒜 ∪ rc73_slice1 i 𝒜).image (insert i)).card = (rc73_slice0 i 𝒜 ∪ rc73_slice1 i 𝒜).card := by
-- proof
  apply StatMech.Walls.rc73_card_high i 𝒜

/--
[rc73_upComp_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc73seqcompress.lean)
-/
@[path]
private lemma rc73_upComp_card_eq
  [DecidableEq α]
  {i : α}
  {𝒜 : Finset (Finset α)} :
-- imply
  (rc73_upComp i 𝒜).card = 𝒜.card := by
-- proof
  apply StatMech.Walls.rc73_upComp_card i 𝒜

/--
[rc73_slice0_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc73seqcompress.lean)
-/
@[path]
private lemma rc73_slice0_box_eq
  [DecidableEq α]
  {i : α}
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  rc73_slice0 i (boxFamily 𝒜 ℬ) = boxFamily (rc73_slice0 i 𝒜) (rc73_slice0 i ℬ) := by
-- proof
  apply StatMech.Walls.rc73_slice0_box i 𝒜 ℬ

/--
[rc73_slice1_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc73seqcompress.lean)
-/
@[path]
private lemma rc73_slice1_box_eq
  [DecidableEq α]
  {i : α}
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  rc73_slice1 i (boxFamily 𝒜 ℬ) = boxFamily (rc73_slice1 i 𝒜) (rc73_slice0 i ℬ) ∪ boxFamily (rc73_slice0 i 𝒜) (rc73_slice1 i ℬ) := by
-- proof
  apply StatMech.Walls.rc73_slice1_box i 𝒜 ℬ

/--
[rc73_slice0_upComp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc73seqcompress.lean)
-/
@[path]
private lemma rc73_slice0_upComp_eq
  [DecidableEq α]
  {i : α}
  {𝒜 : Finset (Finset α)} :
-- imply
  rc73_slice0 i (rc73_upComp i 𝒜) = rc73_slice0 i 𝒜 ∩ rc73_slice1 i 𝒜 := by
-- proof
  apply StatMech.Walls.rc73_slice0_upComp i 𝒜

/--
[rc73_slice1_upComp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc73seqcompress.lean)
-/
@[path]
private lemma rc73_slice1_upComp_eq
  [DecidableEq α]
  {i : α}
  {𝒜 : Finset (Finset α)} :
-- imply
  rc73_slice1 i (rc73_upComp i 𝒜) = rc73_slice0 i 𝒜 ∪ rc73_slice1 i 𝒜 := by
-- proof
  apply StatMech.Walls.rc73_slice1_upComp i 𝒜

/--
[rc73_absentFiber_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc73seqcompress.lean)
-/
@[path]
private lemma rc73_absentFiber_subset_eq
  [DecidableEq α]
  {i : α}
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  rc73_slice0 i (boxFamily (rc73_upComp i 𝒜) (rc73_upComp i ℬ)) ⊆ rc73_slice0 i (boxFamily 𝒜 ℬ) := by
-- proof
  apply StatMech.Walls.rc73_absentFiber_subset i 𝒜 ℬ

/--
[rc73_presentFiber_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc73seqcompress.lean)
-/
@[path]
private lemma rc73_presentFiber_subset_eq
  [DecidableEq α]
  {i : α}
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  rc73_slice1 i (boxFamily (rc73_upComp i 𝒜) (rc73_upComp i ℬ)) ⊆ rc73_slice1 i (boxFamily 𝒜 ℬ) := by
-- proof
  apply StatMech.Walls.rc73_presentFiber_subset i 𝒜 ℬ

/--
[rc73_box_upComp_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc73seqcompress.lean)
-/
@[path]
private lemma rc73_box_upComp_le_eq
  [DecidableEq α]
  {i : α}
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  (boxFamily (rc73_upComp i 𝒜) (rc73_upComp i ℬ)).card ≤ (boxFamily 𝒜 ℬ).card := by
-- proof
  apply StatMech.Walls.rc73_box_upComp_le i 𝒜 ℬ

/--
[rc73_boxFamily_overcounts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc73seqcompress.lean)
-/
@[path]
private lemma rc73_boxFamily_overcounts_eq
  [DecidableEq α] :
-- imply
  2 ^ 2 * (boxFamily reimerStepCexA reimerStepCexB).card > (reimerStepCexA.card * reimerStepCexB.card) ∧ 2 ^ 2 * (rc73_disjOcc reimerStepCexA reimerStepCexB).card ≤ (reimerStepCexA.card * reimerStepCexB.card) := by
-- proof
  apply StatMech.Walls.rc73_boxFamily_overcounts

/--
[rc73_disjOcc_downUp_not_monotone_fin3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc73seqcompress.lean)
-/
@[path]
private lemma rc73_disjOcc_downUp_not_monotone_fin3_eq
  [DecidableEq α] :
-- imply
  (rc73_disjOcc (Down.compression 0 ({∅, {0}, {0, 1}, {2}} : Finset (Finset (Fin 3)))) (rc73_upComp 0 ({∅, {0}, {0, 1}, {0, 2}, {1}, {2}} : Finset (Finset (Fin 3))))).card < (rc73_disjOcc ({∅, {0}, {0, 1}, {2}} : Finset (Finset (Fin 3))) ({∅, {0}, {0, 1}, {0, 2}, {1}, {2}} : Finset (Finset (Fin 3)))).card := by
-- proof
  apply StatMech.Walls.rc73_disjOcc_downUp_not_monotone_fin3

/--
[rc73_reimerWprobCore_of_boxUnionBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc73seqcompress.lean)
-/
@[path]
private lemma rc73_reimerWprobCore_of_boxUnionBound_eq
  [DecidableEq α]
-- given
  (h : rc60_BoxUnionBound) :
-- imply
  ReimerWprobCore := by
-- proof
  apply StatMech.Walls.rc73_reimerWprobCore_of_boxUnionBound h


-- created on 2026-10-23
