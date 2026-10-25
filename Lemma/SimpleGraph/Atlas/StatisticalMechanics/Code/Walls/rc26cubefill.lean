import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc26cubefill
open Finset StatMech StatMech.Walls


/--
[rc26_famCylBox_subset_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc26cubefill.lean)
-/
@[path]
private lemma rc26_famCylBox_subset_left_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  rc20_famCylBox 𝒜 ℬ ⊆ 𝒜 := by
-- proof
  apply StatMech.Walls.rc26_famCylBox_subset_left 𝒜 ℬ

/--
[rc26_famCylBox_subset_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc26cubefill.lean)
-/
@[path]
private lemma rc26_famCylBox_subset_right_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  rc20_famCylBox 𝒜 ℬ ⊆ ℬ := by
-- proof
  apply StatMech.Walls.rc26_famCylBox_subset_right 𝒜 ℬ

/--
[rc26_famCylBox_subset_inter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc26cubefill.lean)
-/
@[path]
private lemma rc26_famCylBox_subset_inter_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  rc20_famCylBox 𝒜 ℬ ⊆ 𝒜 ∩ ℬ := by
-- proof
  apply StatMech.Walls.rc26_famCylBox_subset_inter 𝒜 ℬ

/--
[rc26_reflInter_subset_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc26cubefill.lean)
-/
@[path]
private lemma rc26_reflInter_subset_left_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  rc10_reflInter 𝒜 ℬ ⊆ 𝒜 := by
-- proof
  apply StatMech.Walls.rc26_reflInter_subset_left 𝒜 ℬ

/--
[rc26_both_subset_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc26cubefill.lean)
-/
@[path]
private lemma rc26_both_subset_left_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  rc20_famCylBox 𝒜 ℬ ⊆ 𝒜 ∧ rc10_reflInter 𝒜 ℬ ⊆ 𝒜 := by
-- proof
  apply StatMech.Walls.rc26_both_subset_left 𝒜 ℬ

/--
[rc26_box_not_subset_reflInter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc26cubefill.lean)
-/
@[path]
private lemma rc26_box_not_subset_reflInter_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  ¬ (rc20_famCylBox ({∅, {0}} : Finset (Finset (Fin 3))) ({∅, {1}, {2}, {1,2}}) ⊆ rc10_reflInter ({∅, {0}} : Finset (Finset (Fin 3))) ({∅, {1}, {2}, {1,2}})) := by
-- proof
  apply StatMech.Walls.rc26_box_not_subset_reflInter

/--
[rc26_singleCover_routes_dead](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc26cubefill.lean)
-/
@[path]
private lemma rc26_singleCover_routes_dead_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc22_BoxDownsetBase ∧ (¬ rc22_BoxCompressionMono) ∧ (¬ rc24_BoxDownUpMono) ∧ (∀ [Fintype α] (i : α) (𝒜 ℬ : Finset (Finset α)), #(rc10_reflInter (Down.compression i 𝒜) (Down.compression i ℬ)) ≤ #(rc10_reflInter 𝒜 ℬ)) := by
-- proof
  apply StatMech.Walls.rc26_singleCover_routes_dead

/--
[rc26_cylBoxReflInter_of_boxDoubledCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc26cubefill.lean)
-/
@[path]
private lemma rc26_cylBoxReflInter_of_boxDoubledCount_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : rc25_BoxDoubledCount) :
-- imply
  rc18_CylBoxReflInter := by
-- proof
  apply StatMech.Walls.rc26_cylBoxReflInter_of_boxDoubledCount h

/--
[rc26_boxDoubledCount_iff_reflInter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc26cubefill.lean)
-/
@[path]
private lemma rc26_boxDoubledCount_iff_reflInter_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc25_BoxDoubledCount ↔ ∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))), #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) := by
-- proof
  apply StatMech.Walls.rc26_boxDoubledCount_iff_reflInter

/--
[rc26_boxDoubledCount_strict_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc26cubefill.lean)
-/
@[path]
private lemma rc26_boxDoubledCount_strict_witness_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  #(rc20_famCylBox ({∅, {0}} : Finset (Finset (Fin 3))) ({∅, {1}, {2}, {1,2}, {0,1,2}})) < #(rc22_complPairs ({∅, {0}} : Finset (Finset (Fin 3))) ({∅, {1}, {2}, {1,2}, {0,1,2}})) := by
-- proof
  apply StatMech.Walls.rc26_boxDoubledCount_strict_witness

/--
[rc26_boxDoubledCount_fin2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc26cubefill.lean)
-/
@[path]
private lemma rc26_boxDoubledCount_fin2_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset (Fin 2))} :
-- imply
  #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc22_complPairs 𝒜 ℬ) := by
-- proof
  apply StatMech.Walls.rc26_boxDoubledCount_fin2 𝒜 ℬ

/--
[rc26_reimer_cubefill](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc26cubefill.lean)
-/
@[path]
private lemma rc26_reimer_cubefill_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (∀ (𝒜 ℬ : Finset (Finset α)), rc20_famCylBox 𝒜 ℬ ⊆ 𝒜 ∩ ℬ) ∧ (∀ (𝒜 ℬ : Finset (Finset α)), rc10_reflInter 𝒜 ℬ ⊆ 𝒜) ∧ (¬ (rc20_famCylBox ({∅, {0}} : Finset (Finset (Fin 3))) ({∅, {1}, {2}, {1,2}}) ⊆ rc10_reflInter ({∅, {0}} : Finset (Finset (Fin 3))) ({∅, {1}, {2}, {1,2}}))) ∧ (¬ rc22_BoxCompressionMono) ∧ (¬ rc24_BoxDownUpMono) ∧ rc22_BoxDownsetBase ∧ (rc25_BoxDoubledCount ↔ ∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))), #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ)) ∧ (rc25_BoxDoubledCount → rc18_CylBoxReflInter) := by
-- proof
  apply StatMech.Walls.rc26_reimer_cubefill


-- created on 2026-10-23
