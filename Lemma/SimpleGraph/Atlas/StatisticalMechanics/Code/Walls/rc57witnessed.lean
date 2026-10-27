import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc57witnessed.Part4
open Finset StatMech StatMech.Walls


/--
[rc57_witnessedInter_iff_injection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc57witnessed.lean)
-/
@[path]
private lemma rc57_witnessedInter_iff_injection_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  #((𝒜 ∩ ℬ).filter (rc56_hasWitness 𝒜 ℬ)) ≤ #(𝒜 ∩ rc22_complFam ℬ) ↔ Nonempty (((𝒜 ∩ ℬ).filter (rc56_hasWitness 𝒜 ℬ) : Finset (Finset α)) ↪ (𝒜 ∩ rc22_complFam ℬ : Finset (Finset α))) := by
-- proof
  apply StatMech.Walls.rc57_witnessedInter_iff_injection 𝒜 ℬ

/--
[rc57_naturalSDR_closes_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc57witnessed.lean)
-/
@[path]
private lemma rc57_naturalSDR_closes_residue_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : rc57_NaturalSDR) :
-- imply
  rc20_FamCylBoxResidue := by
-- proof
  apply StatMech.Walls.rc57_naturalSDR_closes_residue h

/--
[rc57_reimer_closes_of_naturalSDR](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc57witnessed.lean)
-/
@[path]
private lemma rc57_reimer_closes_of_naturalSDR_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : rc57_NaturalSDR) :
-- imply
  rc18_CylBoxReflInter := by
-- proof
  apply StatMech.Walls.rc57_reimer_closes_of_naturalSDR h

/--
[rc57_hall_iff_sdr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc57witnessed.lean)
-/
@[path]
private lemma rc57_hall_iff_sdr_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))} :
-- imply
  (∀ 𝒮 : Finset (rc20_famCylBox 𝒜 ℬ), #𝒮 ≤ #(𝒮.biUnion (fun S => rc21_admComp n 𝒜 ℬ (S : Finset (Fin n))))) ↔ ∃ f : (rc20_famCylBox 𝒜 ℬ) → Finset (Fin n), Function.Injective f ∧ ∀ S : (rc20_famCylBox 𝒜 ℬ), f S ∈ rc21_admComp n 𝒜 ℬ (S : Finset (Fin n)) := by
-- proof
  apply StatMech.Walls.rc57_hall_iff_sdr n 𝒜 ℬ

/--
[rc57_box_natRes_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc57witnessed.lean)
-/
@[path]
private lemma rc57_box_natRes_card_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (rc20_famCylBoxComp 3 rc57_Anat rc57_Bnat).card = 2 := by
-- proof
  apply StatMech.Walls.rc57_box_natRes_card

/--
[rc57_reflInter_natRes_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc57witnessed.lean)
-/
@[path]
private lemma rc57_reflInter_natRes_card_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (rc20_reflInterComp 3 rc57_Anat rc57_Bnat).card = 3 := by
-- proof
  apply StatMech.Walls.rc57_reflInter_natRes_card

/--
[rc57_natNbhd_natRes_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc57witnessed.lean)
-/
@[path]
private lemma rc57_natNbhd_natRes_card_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (rc57_natNbhd 3 rc57_Anat rc57_Bnat).card = 1 := by
-- proof
  apply StatMech.Walls.rc57_natNbhd_natRes_card

/--
[rc57_naturalHall_fails_fin3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc57witnessed.lean)
-/
@[path]
private lemma rc57_naturalHall_fails_fin3_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (rc57_natNbhd 3 rc57_Anat rc57_Bnat).card < (rc20_famCylBoxComp 3 rc57_Anat rc57_Bnat).card := by
-- proof
  apply StatMech.Walls.rc57_naturalHall_fails_fin3

/--
[rc57_wall_holds_on_natRes](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc57witnessed.lean)
-/
@[path]
private lemma rc57_wall_holds_on_natRes_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (rc20_famCylBoxComp 3 rc57_Anat rc57_Bnat).card ≤ (rc20_reflInterComp 3 rc57_Anat rc57_Bnat).card := by
-- proof
  apply StatMech.Walls.rc57_wall_holds_on_natRes

/--
[rc57_reflMatching_iff_witnessedInterResidue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc57witnessed.lean)
-/
@[path]
private lemma rc57_reflMatching_iff_witnessedInterResidue_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc57_ReflMatching ↔ rc56_WitnessedInterResidue := by
-- proof
  apply StatMech.Walls.rc57_reflMatching_iff_witnessedInterResidue

/--
[rc57_reimer_closes_of_reflMatching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc57witnessed.lean)
-/
@[path]
private lemma rc57_reimer_closes_of_reflMatching_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : rc57_ReflMatching) :
-- imply
  rc18_CylBoxReflInter := by
-- proof
  apply StatMech.Walls.rc57_reimer_closes_of_reflMatching h

/--
[rc57_reimer_matching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc57witnessed.lean)
-/
@[path]
private lemma rc57_reimer_matching_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (∀ (𝒜 ℬ : Finset (Finset (Fin 3))), #((𝒜 ∩ ℬ).filter (rc56_hasWitness 𝒜 ℬ)) ≤ #(𝒜 ∩ rc22_complFam ℬ) ↔ Nonempty (((𝒜 ∩ ℬ).filter (rc56_hasWitness 𝒜 ℬ) : Finset (Finset (Fin 3))) ↪ (𝒜 ∩ rc22_complFam ℬ : Finset (Finset (Fin 3))))) ∧ (rc57_ReflMatching ↔ rc56_WitnessedInterResidue) ∧ (rc57_ReflMatching → rc18_CylBoxReflInter) ∧ (rc57_NaturalSDR → rc18_CylBoxReflInter) ∧ ((rc57_natNbhd 3 rc57_Anat rc57_Bnat).card < (rc20_famCylBoxComp 3 rc57_Anat rc57_Bnat).card) ∧ ((rc20_famCylBoxComp 3 rc57_Anat rc57_Bnat).card ≤ (rc20_reflInterComp 3 rc57_Anat rc57_Bnat).card) := by
-- proof
  apply StatMech.Walls.rc57_reimer_matching


-- created on 2026-10-23
