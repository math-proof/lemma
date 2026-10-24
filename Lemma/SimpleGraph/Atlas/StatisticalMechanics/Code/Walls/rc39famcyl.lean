import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.rc39famcyl
open Finset StatMech StatMech.Walls


/--
[rc39_reflInter_right_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc39famcyl.lean)
-/
@[path]
private lemma rc39_reflInter_right_univ_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 : Finset (Finset α)} :
-- imply
  rc10_reflInter 𝒜 univ = 𝒜 := by
-- proof
  apply StatMech.Walls.rc39_reflInter_right_univ 𝒜

/--
[rc39_famCylBox_right_univ_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc39famcyl.lean)
-/
@[path]
private lemma rc39_famCylBox_right_univ_subset_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 : Finset (Finset α)} :
-- imply
  rc20_famCylBox 𝒜 univ ⊆ 𝒜 := by
-- proof
  apply StatMech.Walls.rc39_famCylBox_right_univ_subset 𝒜

/--
[rc39_famCylBox_le_reflInter_right_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc39famcyl.lean)
-/
@[path]
private lemma rc39_famCylBox_le_reflInter_right_univ_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 : Finset (Finset α)} :
-- imply
  #(rc20_famCylBox 𝒜 univ) ≤ #(rc10_reflInter 𝒜 univ) := by
-- proof
  apply StatMech.Walls.rc39_famCylBox_le_reflInter_right_univ 𝒜

/--
[rc39_famCylBox_left_univ_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc39famcyl.lean)
-/
@[path]
private lemma rc39_famCylBox_left_univ_subset_eq
  [Fintype α]
  [DecidableEq α]
  {ℬ : Finset (Finset α)} :
-- imply
  rc20_famCylBox univ ℬ ⊆ ℬ := by
-- proof
  apply StatMech.Walls.rc39_famCylBox_left_univ_subset ℬ

/--
[rc39_card_reflInter_left_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc39famcyl.lean)
-/
@[path]
private lemma rc39_card_reflInter_left_univ_eq
  [Fintype α]
  [DecidableEq α]
  {ℬ : Finset (Finset α)} :
-- imply
  #(rc10_reflInter univ ℬ) = #ℬ := by
-- proof
  apply StatMech.Walls.rc39_card_reflInter_left_univ ℬ

/--
[rc39_famCylBox_le_reflInter_left_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc39famcyl.lean)
-/
@[path]
private lemma rc39_famCylBox_le_reflInter_left_univ_eq
  [Fintype α]
  [DecidableEq α]
  {ℬ : Finset (Finset α)} :
-- imply
  #(rc20_famCylBox univ ℬ) ≤ #(rc10_reflInter univ ℬ) := by
-- proof
  apply StatMech.Walls.rc39_famCylBox_le_reflInter_left_univ ℬ

/--
[rc39_famCylBox_le_reflInter_of_monotone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc39famcyl.lean)
-/
@[path]
private lemma rc39_famCylBox_le_reflInter_of_monotone_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
-- given
  (h : (IsUpperSet (𝒜 : Set (Finset (Fin n))) ∧ IsUpperSet (ℬ : Set (Finset (Fin n)))) ∨ (IsLowerSet (𝒜 : Set (Finset (Fin n))) ∧ IsLowerSet (ℬ : Set (Finset (Fin n))))) :
-- imply
  #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) := by
-- proof
  apply StatMech.Walls.rc39_famCylBox_le_reflInter_of_monotone h

/--
[rc39_deficit_downDown_strictIncrease](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc39famcyl.lean)
-/
@[path]
private lemma rc39_deficit_downDown_strictIncrease_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (#(rc10_reflInter dc39_A dc39_B) - #(rc20_famCylBox dc39_A dc39_B)) < (#(rc10_reflInter (Down.compression 0 dc39_A) (Down.compression 0 dc39_B)) - #(rc20_famCylBox (Down.compression 0 dc39_A) (Down.compression 0 dc39_B))) := by
-- proof
  apply StatMech.Walls.rc39_deficit_downDown_strictIncrease

/--
[rc39_deficitMono_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc39famcyl.lean)
-/
@[path]
private lemma rc39_deficitMono_false_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  ¬ (∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) (i : Fin n), (#(rc10_reflInter (Down.compression i 𝒜) (Down.compression i ℬ)) - #(rc20_famCylBox (Down.compression i 𝒜) (Down.compression i ℬ))) ≤ (#(rc10_reflInter 𝒜 ℬ) - #(rc20_famCylBox 𝒜 ℬ))) := by
-- proof
  apply StatMech.Walls.rc39_deficitMono_false

/--
[rc39_famCylBox_oneSide_strictDecrease](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc39famcyl.lean)
-/
@[path]
private lemma rc39_famCylBox_oneSide_strictDecrease_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  #(rc20_famCylBox (Down.compression 0 dc39_C) dc39_D) < #(rc20_famCylBox dc39_C dc39_D) := by
-- proof
  apply StatMech.Walls.rc39_famCylBox_oneSide_strictDecrease

/--
[rc39_boxOneSideMono_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc39famcyl.lean)
-/
@[path]
private lemma rc39_boxOneSideMono_false_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  ¬ (∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) (i : Fin n), #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc20_famCylBox (Down.compression i 𝒜) ℬ)) := by
-- proof
  apply StatMech.Walls.rc39_boxOneSideMono_false

/--
[rc39_reflInter_oneSide_strictIncrease](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc39famcyl.lean)
-/
@[path]
private lemma rc39_reflInter_oneSide_strictIncrease_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  #(rc10_reflInter dc39_E dc39_F) < #(rc10_reflInter (Down.compression 0 dc39_E) dc39_F) := by
-- proof
  apply StatMech.Walls.rc39_reflInter_oneSide_strictIncrease

/--
[rc39_reflInter_oneSide_antitone_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc39famcyl.lean)
-/
@[path]
private lemma rc39_reflInter_oneSide_antitone_false_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  ¬ (∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) (i : Fin n), #(rc10_reflInter (Down.compression i 𝒜) ℬ) ≤ #(rc10_reflInter 𝒜 ℬ)) := by
-- proof
  apply StatMech.Walls.rc39_reflInter_oneSide_antitone_false

/--
[rc39_wall_holds_deficitWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc39famcyl.lean)
-/
@[path]
private lemma rc39_wall_holds_deficitWitness_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  #(rc20_famCylBox dc39_A dc39_B) ≤ #(rc10_reflInter dc39_A dc39_B) := by
-- proof
  apply StatMech.Walls.rc39_wall_holds_deficitWitness

/--
[rc39_wall_holds_boxOneSideWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc39famcyl.lean)
-/
@[path]
private lemma rc39_wall_holds_boxOneSideWitness_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  #(rc20_famCylBox dc39_C dc39_D) ≤ #(rc10_reflInter dc39_C dc39_D) := by
-- proof
  apply StatMech.Walls.rc39_wall_holds_boxOneSideWitness

/--
[rc39_wall_holds_reflOneSideWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc39famcyl.lean)
-/
@[path]
private lemma rc39_wall_holds_reflOneSideWitness_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  #(rc20_famCylBox dc39_E dc39_F) ≤ #(rc10_reflInter dc39_E dc39_F) := by
-- proof
  apply StatMech.Walls.rc39_wall_holds_reflOneSideWitness

/--
[rc39_reimer_famcyl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc39famcyl.lean)
-/
@[path]
private lemma rc39_reimer_famcyl_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (∀ (𝒜 : Finset (Finset α)), #(rc20_famCylBox 𝒜 univ) ≤ #(rc10_reflInter 𝒜 univ)) ∧ (∀ (ℬ : Finset (Finset α)), #(rc20_famCylBox univ ℬ) ≤ #(rc10_reflInter univ ℬ)) ∧ (∀ {n : ℕ} {𝒜 ℬ : Finset (Finset (Fin n))}, (IsUpperSet (𝒜 : Set (Finset (Fin n))) ∧ IsUpperSet (ℬ : Set (Finset (Fin n)))) ∨ (IsLowerSet (𝒜 : Set (Finset (Fin n))) ∧ IsLowerSet (ℬ : Set (Finset (Fin n)))) → #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ)) ∧ (¬ (∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) (i : Fin n), (#(rc10_reflInter (Down.compression i 𝒜) (Down.compression i ℬ)) - #(rc20_famCylBox (Down.compression i 𝒜) (Down.compression i ℬ))) ≤ (#(rc10_reflInter 𝒜 ℬ) - #(rc20_famCylBox 𝒜 ℬ)))) ∧ (¬ (∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) (i : Fin n), #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc20_famCylBox (Down.compression i 𝒜) ℬ))) ∧ (¬ (∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) (i : Fin n), #(rc10_reflInter (Down.compression i 𝒜) ℬ) ≤ #(rc10_reflInter 𝒜 ℬ))) := by
-- proof
  apply StatMech.Walls.rc39_reimer_famcyl


-- created on 2026-10-23
