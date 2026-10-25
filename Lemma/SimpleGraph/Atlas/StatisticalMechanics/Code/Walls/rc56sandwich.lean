import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc56sandwich.Part3
open Finset StatMech StatMech.Walls


/--
[rc56_mem_famCylBox_iff_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc56sandwich.lean)
-/
@[path]
private lemma rc56_mem_famCylBox_iff_witness_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {S : Finset α} :
-- imply
  S ∈ rc20_famCylBox 𝒜 ℬ ↔ rc56_hasWitness 𝒜 ℬ S := by
-- proof
  apply StatMech.Walls.rc56_mem_famCylBox_iff_witness 𝒜 ℬ S

/--
[rc56_mem_inter_of_hasWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc56sandwich.lean)
-/
@[path]
private lemma rc56_mem_inter_of_hasWitness_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {S : Finset α}
-- given
  (h : rc56_hasWitness 𝒜 ℬ S) :
-- imply
  S ∈ 𝒜 ∩ ℬ := by
-- proof
  apply StatMech.Walls.rc56_mem_inter_of_hasWitness 𝒜 ℬ h

/--
[rc56_famCylBox_eq_inter_filter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc56sandwich.lean)
-/
@[path]
private lemma rc56_famCylBox_eq_inter_filter_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  rc20_famCylBox 𝒜 ℬ = (𝒜 ∩ ℬ).filter (rc56_hasWitness 𝒜 ℬ) := by
-- proof
  apply StatMech.Walls.rc56_famCylBox_eq_inter_filter 𝒜 ℬ

/--
[rc56_famCylBox_card_eq_witnessCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc56sandwich.lean)
-/
@[path]
private lemma rc56_famCylBox_card_eq_witnessCount_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  #(rc20_famCylBox 𝒜 ℬ) = #((𝒜 ∩ ℬ).filter (rc56_hasWitness 𝒜 ℬ)) := by
-- proof
  apply StatMech.Walls.rc56_famCylBox_card_eq_witnessCount 𝒜 ℬ

/--
[rc56_famCylBox_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc56sandwich.lean)
-/
@[path]
private lemma rc56_famCylBox_symm_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  rc20_famCylBox 𝒜 ℬ = rc20_famCylBox ℬ 𝒜 := by
-- proof
  apply StatMech.Walls.rc56_famCylBox_symm 𝒜 ℬ

/--
[rc56_famCylBox_card_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc56sandwich.lean)
-/
@[path]
private lemma rc56_famCylBox_card_symm_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  #(rc20_famCylBox 𝒜 ℬ) = #(rc20_famCylBox ℬ 𝒜) := by
-- proof
  apply StatMech.Walls.rc56_famCylBox_card_symm 𝒜 ℬ

/--
[rc56_reflInter_card_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc56sandwich.lean)
-/
@[path]
private lemma rc56_reflInter_card_symm_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  #(rc10_reflInter 𝒜 ℬ) = #(rc10_reflInter ℬ 𝒜) := by
-- proof
  apply StatMech.Walls.rc56_reflInter_card_symm 𝒜 ℬ

/--
[rc56_reflInter_card_eq_interComplFam](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc56sandwich.lean)
-/
@[path]
private lemma rc56_reflInter_card_eq_interComplFam_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  #(rc10_reflInter 𝒜 ℬ) = #(𝒜 ∩ rc22_complFam ℬ) := by
-- proof
  apply StatMech.Walls.rc56_reflInter_card_eq_interComplFam 𝒜 ℬ

/--
[rc56_wall_iff_witnessedInter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc56sandwich.lean)
-/
@[path]
private lemma rc56_wall_iff_witnessedInter_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) ↔ #((𝒜 ∩ ℬ).filter (rc56_hasWitness 𝒜 ℬ)) ≤ #(𝒜 ∩ rc22_complFam ℬ) := by
-- proof
  apply StatMech.Walls.rc56_wall_iff_witnessedInter 𝒜 ℬ

/--
[rc56_witnessedInterResidue_iff_famCylBoxResidue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc56sandwich.lean)
-/
@[path]
private lemma rc56_witnessedInterResidue_iff_famCylBoxResidue_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc56_WitnessedInterResidue ↔ rc20_FamCylBoxResidue := by
-- proof
  apply StatMech.Walls.rc56_witnessedInterResidue_iff_famCylBoxResidue

/--
[rc56_reimer_closes_of_witnessedInterResidue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc56sandwich.lean)
-/
@[path]
private lemma rc56_reimer_closes_of_witnessedInterResidue_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : rc56_WitnessedInterResidue) :
-- imply
  rc18_CylBoxReflInter := by
-- proof
  apply StatMech.Walls.rc56_reimer_closes_of_witnessedInterResidue h

/--
[rc56_box_res_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc56sandwich.lean)
-/
@[path]
private lemma rc56_box_res_card_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (rc20_famCylBoxComp 3 rc56_Ares rc56_Bres).card = 2 := by
-- proof
  apply StatMech.Walls.rc56_box_res_card

/--
[rc56_reflInter_res_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc56sandwich.lean)
-/
@[path]
private lemma rc56_reflInter_res_card_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (rc20_reflInterComp 3 rc56_Ares rc56_Bres).card = 3 := by
-- proof
  apply StatMech.Walls.rc56_reflInter_res_card

/--
[rc56_reflImageSet_res_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc56sandwich.lean)
-/
@[path]
private lemma rc56_reflImageSet_res_card_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (rc56_reflImageSet 3 rc56_Ares rc56_Bres).card = 1 := by
-- proof
  apply StatMech.Walls.rc56_reflImageSet_res_card

/--
[rc56_symmDiff_collides_fin3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc56sandwich.lean)
-/
@[path]
private lemma rc56_symmDiff_collides_fin3_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (rc56_reflImageSet 3 rc56_Ares rc56_Bres).card < (rc20_famCylBoxComp 3 rc56_Ares rc56_Bres).card := by
-- proof
  apply StatMech.Walls.rc56_symmDiff_collides_fin3

/--
[rc56_wall_holds_on_res](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc56sandwich.lean)
-/
@[path]
private lemma rc56_wall_holds_on_res_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (rc20_famCylBoxComp 3 rc56_Ares rc56_Bres).card ≤ (rc20_reflInterComp 3 rc56_Ares rc56_Bres).card := by
-- proof
  apply StatMech.Walls.rc56_wall_holds_on_res

/--
[rc56_reimer_closes_of_famCylBoxResidue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc56sandwich.lean)
-/
@[path]
private lemma rc56_reimer_closes_of_famCylBoxResidue_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : rc20_FamCylBoxResidue) :
-- imply
  rc18_CylBoxReflInter := by
-- proof
  apply StatMech.Walls.rc56_reimer_closes_of_famCylBoxResidue h

/--
[rc56_reimerWprobCore_of_famCylBoxResidue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc56sandwich.lean)
-/
@[path]
private lemma rc56_reimerWprobCore_of_famCylBoxResidue_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : rc20_FamCylBoxResidue) :
-- imply
  ReimerWprobCore := by
-- proof
  apply StatMech.Walls.rc56_reimerWprobCore_of_famCylBoxResidue h

/--
[rc56_reimer_sandwich](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc56sandwich.lean)
-/
@[path]
private lemma rc56_reimer_sandwich_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (∀ (𝒜 ℬ : Finset (Finset (Fin 3))), rc20_famCylBox 𝒜 ℬ = (𝒜 ∩ ℬ).filter (rc56_hasWitness 𝒜 ℬ)) ∧ (∀ (𝒜 ℬ : Finset (Finset (Fin 3))), rc20_famCylBox 𝒜 ℬ = rc20_famCylBox ℬ 𝒜) ∧ (∀ (𝒜 ℬ : Finset (Finset (Fin 3))), #(rc10_reflInter 𝒜 ℬ) = #(rc10_reflInter ℬ 𝒜)) ∧ (∀ (𝒜 ℬ : Finset (Finset (Fin 3))), #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) ↔ #((𝒜 ∩ ℬ).filter (rc56_hasWitness 𝒜 ℬ)) ≤ #(𝒜 ∩ rc22_complFam ℬ)) ∧ (rc56_WitnessedInterResidue ↔ rc20_FamCylBoxResidue) ∧ (rc56_WitnessedInterResidue → rc18_CylBoxReflInter) ∧ ((rc56_reflImageSet 3 rc56_Ares rc56_Bres).card < (rc20_famCylBoxComp 3 rc56_Ares rc56_Bres).card) ∧ ((rc20_famCylBoxComp 3 rc56_Ares rc56_Bres).card ≤ (rc20_reflInterComp 3 rc56_Ares rc56_Bres).card) := by
-- proof
  apply StatMech.Walls.rc56_reimer_sandwich


-- created on 2026-10-23
