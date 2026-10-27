import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc47reimer.Part3
open Finset StatMech StatMech.Walls


/--
[rc47_famCylBox_subset_inter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc47reimer.lean)
-/
@[path]
private lemma rc47_famCylBox_subset_inter_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  rc20_famCylBox 𝒜 ℬ ⊆ 𝒜 ∩ ℬ := by
-- proof
  apply StatMech.Walls.rc47_famCylBox_subset_inter 𝒜 ℬ

/--
[rc47_famCylBox_subset_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc47reimer.lean)
-/
@[path]
private lemma rc47_famCylBox_subset_left_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  rc20_famCylBox 𝒜 ℬ ⊆ 𝒜 := by
-- proof
  apply StatMech.Walls.rc47_famCylBox_subset_left 𝒜 ℬ

/--
[rc47_famCylBox_subset_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc47reimer.lean)
-/
@[path]
private lemma rc47_famCylBox_subset_right_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  rc20_famCylBox 𝒜 ℬ ⊆ ℬ := by
-- proof
  apply StatMech.Walls.rc47_famCylBox_subset_right 𝒜 ℬ

/--
[rc47_reflInter_subset_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc47reimer.lean)
-/
@[path]
private lemma rc47_reflInter_subset_left_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  rc10_reflInter 𝒜 ℬ ⊆ 𝒜 := by
-- proof
  apply StatMech.Walls.rc47_reflInter_subset_left 𝒜 ℬ

/--
[rc47_reflInter_card_le_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc47reimer.lean)
-/
@[path]
private lemma rc47_reflInter_card_le_right_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  #(rc10_reflInter 𝒜 ℬ) ≤ #ℬ := by
-- proof
  apply StatMech.Walls.rc47_reflInter_card_le_right 𝒜 ℬ

/--
[rc47_reflInter_card_le_min](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc47reimer.lean)
-/
@[path]
private lemma rc47_reflInter_card_le_min_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  #(rc10_reflInter 𝒜 ℬ) ≤ min (#𝒜) (#ℬ) := by
-- proof
  apply StatMech.Walls.rc47_reflInter_card_le_min 𝒜 ℬ

/--
[rc47_famCylBox_card_le_min](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc47reimer.lean)
-/
@[path]
private lemma rc47_famCylBox_card_le_min_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  #(rc20_famCylBox 𝒜 ℬ) ≤ min (#𝒜) (#ℬ) := by
-- proof
  apply StatMech.Walls.rc47_famCylBox_card_le_min 𝒜 ℬ

/--
[rc47_famCylBox_le_reflInter_of_interCard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc47reimer.lean)
-/
@[path]
private lemma rc47_famCylBox_le_reflInter_of_interCard_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
-- given
  (h : #(𝒜 ∩ ℬ) ≤ #(rc10_reflInter 𝒜 ℬ)) :
-- imply
  #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) := by
-- proof
  apply StatMech.Walls.rc47_famCylBox_le_reflInter_of_interCard 𝒜 ℬ h

/--
[rc47_famCylBox_le_reflInter_of_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc47reimer.lean)
-/
@[path]
private lemma rc47_famCylBox_le_reflInter_of_subset_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
-- given
  (h : rc20_famCylBox 𝒜 ℬ ⊆ rc10_reflInter 𝒜 ℬ) :
-- imply
  #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) := by
-- proof
  apply StatMech.Walls.rc47_famCylBox_le_reflInter_of_subset 𝒜 ℬ h

/--
[rc47_reimer_closes_of_interCardDominatesAll](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc47reimer.lean)
-/
@[path]
private lemma rc47_reimer_closes_of_interCardDominatesAll_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : rc47_InterCardDominatesAll) :
-- imply
  rc18_CylBoxReflInter := by
-- proof
  apply StatMech.Walls.rc47_reimer_closes_of_interCardDominatesAll h

/--
[rc47_interCard_fires_rc40_fin3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc47reimer.lean)
-/
@[path]
private lemma rc47_interCard_fires_rc40_fin3_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  #(rc40_Aref ∩ rc40_Bref) ≤ (rc20_reflInterComp 3 rc40_Aref rc40_Bref).card := by
-- proof
  apply StatMech.Walls.rc47_interCard_fires_rc40_fin3

/--
[rc47_wall_rc40_via_interCard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc47reimer.lean)
-/
@[path]
private lemma rc47_wall_rc40_via_interCard_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  #(rc20_famCylBox rc40_Aref rc40_Bref) ≤ #(rc10_reflInter rc40_Aref rc40_Bref) := by
-- proof
  apply StatMech.Walls.rc47_wall_rc40_via_interCard

/--
[rc47_interCard_not_universal_fin3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc47reimer.lean)
-/
@[path]
private lemma rc47_interCard_not_universal_fin3_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (rc20_reflInterComp 3 rc47_A₁ rc47_B₁).card < #(rc47_A₁ ∩ rc47_B₁) := by
-- proof
  apply StatMech.Walls.rc47_interCard_not_universal_fin3

/--
[rc47_wall_A](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc47reimer.lean)
-/
@[path]
private lemma rc47_wall_A_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (rc20_famCylBoxComp 3 rc47_A₁ rc47_B₁).card ≤ (rc20_reflInterComp 3 rc47_A₁ rc47_B₁).card := by
-- proof
  apply StatMech.Walls.rc47_wall_A

/--
[rc47_boxSubReflInter_fires_fin3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc47reimer.lean)
-/
@[path]
private lemma rc47_boxSubReflInter_fires_fin3_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc20_famCylBoxComp 3 rc47_A₁ rc47_B₃ ⊆ rc20_reflInterComp 3 rc47_A₁ rc47_B₃ := by
-- proof
  apply StatMech.Walls.rc47_boxSubReflInter_fires_fin3

/--
[rc47_boxSubReflInter_fails_fin3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc47reimer.lean)
-/
@[path]
private lemma rc47_boxSubReflInter_fails_fin3_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  ¬ (rc20_famCylBoxComp 3 rc47_A₁ rc47_B₂ ⊆ rc20_reflInterComp 3 rc47_A₁ rc47_B₂) := by
-- proof
  apply StatMech.Walls.rc47_boxSubReflInter_fails_fin3

/--
[rc47_reimer_closes_of_famCylBoxResidue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc47reimer.lean)
-/
@[path]
private lemma rc47_reimer_closes_of_famCylBoxResidue_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : rc20_FamCylBoxResidue) :
-- imply
  rc18_CylBoxReflInter := by
-- proof
  apply StatMech.Walls.rc47_reimer_closes_of_famCylBoxResidue h

/--
[rc47_reimer_sandwich](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc47reimer.lean)
-/
@[path]
private lemma rc47_reimer_sandwich_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (∀ (𝒜 ℬ : Finset (Finset (Fin 3))), rc20_famCylBox 𝒜 ℬ ⊆ 𝒜 ∩ ℬ) ∧ (∀ (𝒜 ℬ : Finset (Finset (Fin 3))), #(rc20_famCylBox 𝒜 ℬ) ≤ min (#𝒜) (#ℬ)) ∧ (∀ (𝒜 ℬ : Finset (Finset (Fin 3))), #(rc10_reflInter 𝒜 ℬ) ≤ min (#𝒜) (#ℬ)) ∧ (∀ (𝒜 ℬ : Finset (Finset (Fin 3))), #(𝒜 ∩ ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) → #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ)) ∧ (rc47_InterCardDominatesAll → rc18_CylBoxReflInter) ∧ (#(rc20_famCylBox rc40_Aref rc40_Bref) ≤ #(rc10_reflInter rc40_Aref rc40_Bref)) ∧ ((rc20_reflInterComp 3 rc47_A₁ rc47_B₁).card < #(rc47_A₁ ∩ rc47_B₁)) ∧ (¬ (rc20_famCylBoxComp 3 rc47_A₁ rc47_B₂ ⊆ rc20_reflInterComp 3 rc47_A₁ rc47_B₂)) := by
-- proof
  apply StatMech.Walls.rc47_reimer_sandwich


-- created on 2026-10-23
