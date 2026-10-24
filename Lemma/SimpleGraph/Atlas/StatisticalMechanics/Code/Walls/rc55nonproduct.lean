import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.rc55nonproduct
open Finset StatMech StatMech.Walls


/--
[rc55_famCylBox_downDown_strictly_decreases_fin3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc55nonproduct.lean)
-/
@[path]
private lemma rc55_famCylBox_downDown_strictly_decreases_fin3_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  #(rc20_famCylBox (Down.compression 1 rc46_Adn) (Down.compression 1 rc46_Bdn)) < #(rc20_famCylBox rc46_Adn rc46_Bdn) := by
-- proof
  apply StatMech.Walls.rc55_famCylBox_downDown_strictly_decreases_fin3

/--
[rc55_boxCompressionMono_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc55nonproduct.lean)
-/
@[path]
private lemma rc55_boxCompressionMono_false_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  ¬ rc22_BoxCompressionMono := by
-- proof
  apply StatMech.Walls.rc55_boxCompressionMono_false

/--
[rc55_leftProj_dbl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc55nonproduct.lean)
-/
@[path]
private lemma rc55_leftProj_dbl_eq
  [Fintype α]
  [DecidableEq α]
  {S T : Finset α} :
-- imply
  rc55_leftProj (dbl S T) = S := by
-- proof
  apply StatMech.Walls.rc55_leftProj_dbl S T

/--
[rc55_rightProj_dbl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc55nonproduct.lean)
-/
@[path]
private lemma rc55_rightProj_dbl_eq
  [Fintype α]
  [DecidableEq α]
  {S T : Finset α} :
-- imply
  rc55_rightProj (dbl S T) = T := by
-- proof
  apply StatMech.Walls.rc55_rightProj_dbl S T

/--
[rc55_dbl_compl_isSuperfill](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc55nonproduct.lean)
-/
@[path]
private lemma rc55_dbl_compl_isSuperfill_eq
  [Fintype α]
  [DecidableEq α]
  {R : Finset α} :
-- imply
  rc55_isSuperfill (dbl R Rᶜ) := by
-- proof
  apply StatMech.Walls.rc55_dbl_compl_isSuperfill R

/--
[rc55_disjoint_fill_iff_compl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc55nonproduct.lean)
-/
@[path]
private lemma rc55_disjoint_fill_iff_compl_eq
  [Fintype α]
  [DecidableEq α]
  {S T : Finset α}
-- given
  (hd : Disjoint S T) :
-- imply
  S ∪ T = univ ↔ T = Sᶜ := by
-- proof
  apply StatMech.Walls.rc55_disjoint_fill_iff_compl hd

/--
[rc55_superfill_filter_boxDoubled](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc55nonproduct.lean)
-/
@[path]
private lemma rc55_superfill_filter_boxDoubled_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  (boxDoubled 𝒜 ℬ).filter rc55_isSuperfill = rc37_complBoxDoubled 𝒜 ℬ := by
-- proof
  apply StatMech.Walls.rc55_superfill_filter_boxDoubled 𝒜 ℬ

/--
[rc55_superfillCount_boxDoubled_eq_reflInter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc55nonproduct.lean)
-/
@[path]
private lemma rc55_superfillCount_boxDoubled_eq_reflInter_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  rc55_superfillCount (boxDoubled 𝒜 ℬ) = #(rc10_reflInter 𝒜 ℬ) := by
-- proof
  apply StatMech.Walls.rc55_superfillCount_boxDoubled_eq_reflInter 𝒜 ℬ

/--
[rc55_superfillCount_refuter_start](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc55nonproduct.lean)
-/
@[path]
private lemma rc55_superfillCount_refuter_start_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc55_superfillCount (boxDoubled rc46_Adn rc46_Bdn) = 2 := by
-- proof
  apply StatMech.Walls.rc55_superfillCount_refuter_start

/--
[rc55_superfillCount_refuter_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc55nonproduct.lean)
-/
@[path]
private lemma rc55_superfillCount_refuter_step_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc55_superfillCount (doubleCompress 1 (boxDoubled rc46_Adn rc46_Bdn)) = 3 := by
-- proof
  apply StatMech.Walls.rc55_superfillCount_refuter_step

/--
[rc55_superfill_nondecreasing_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc55nonproduct.lean)
-/
@[path]
private lemma rc55_superfill_nondecreasing_witness_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc55_superfillCount (boxDoubled rc46_Adn rc46_Bdn) ≤ rc55_superfillCount (doubleCompress 1 (boxDoubled rc46_Adn rc46_Bdn)) := by
-- proof
  apply StatMech.Walls.rc55_superfill_nondecreasing_witness

/--
[rc55_reflInter_le_boxDoubled](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc55nonproduct.lean)
-/
@[path]
private lemma rc55_reflInter_le_boxDoubled_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  #(rc10_reflInter 𝒜 ℬ) ≤ #(boxDoubled 𝒜 ℬ) := by
-- proof
  apply StatMech.Walls.rc55_reflInter_le_boxDoubled 𝒜 ℬ

/--
[rc55_boxDownsetBase_fin0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc55nonproduct.lean)
-/
@[path]
private lemma rc55_boxDownsetBase_fin0_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset (Fin 0))} :
-- imply
  #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) := by
-- proof
  apply StatMech.Walls.rc55_boxDownsetBase_fin0 𝒜 ℬ

/--
[rc55_boxDownsetBase_upperSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc55nonproduct.lean)
-/
@[path]
private lemma rc55_boxDownsetBase_upperSet_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
-- given
  (h𝒜 : IsUpperSet (𝒜 : Set (Finset (Fin n))))
  (hℬ : IsUpperSet (ℬ : Set (Finset (Fin n)))) :
-- imply
  #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) := by
-- proof
  apply StatMech.Walls.rc55_boxDownsetBase_upperSet h𝒜 hℬ

/--
[rc55_reimer_of_hallDoubled](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc55nonproduct.lean)
-/
@[path]
private lemma rc55_reimer_of_hallDoubled_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : rc37_HallDoubled) :
-- imply
  rc18_CylBoxReflInter := by
-- proof
  apply StatMech.Walls.rc55_reimer_of_hallDoubled h

/--
[rc55_famCylBoxResidue_of_hallDoubled](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc55nonproduct.lean)
-/
@[path]
private lemma rc55_famCylBoxResidue_of_hallDoubled_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : rc37_HallDoubled) :
-- imply
  rc20_FamCylBoxResidue := by
-- proof
  apply StatMech.Walls.rc55_famCylBoxResidue_of_hallDoubled h

/--
[rc55_reimerWprobCore_of_famCylBoxResidue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc55nonproduct.lean)
-/
@[path]
private lemma rc55_reimerWprobCore_of_famCylBoxResidue_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : rc20_FamCylBoxResidue) :
-- imply
  ReimerWprobCore := by
-- proof
  apply StatMech.Walls.rc55_reimerWprobCore_of_famCylBoxResidue h

/--
[rc55_wall_holds_on_refuter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc55nonproduct.lean)
-/
@[path]
private lemma rc55_wall_holds_on_refuter_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (rc20_famCylBoxComp 3 rc46_Adn rc46_Bdn).card ≤ (rc20_reflInterComp 3 rc46_Adn rc46_Bdn).card := by
-- proof
  apply StatMech.Walls.rc55_wall_holds_on_refuter

/--
[rc55_reimer_nonproduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc55nonproduct.lean)
-/
@[path]
private lemma rc55_reimer_nonproduct_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (¬ rc22_BoxCompressionMono) ∧ (∀ (𝒜 ℬ : Finset (Finset (Fin 3))), rc55_superfillCount (boxDoubled 𝒜 ℬ) = #(rc10_reflInter 𝒜 ℬ)) ∧ (rc55_superfillCount (boxDoubled rc46_Adn rc46_Bdn) ≤ rc55_superfillCount (doubleCompress 1 (boxDoubled rc46_Adn rc46_Bdn))) ∧ (∀ (𝒜 ℬ : Finset (Finset (Fin 3))), #(rc10_reflInter 𝒜 ℬ) ≤ #(boxDoubled 𝒜 ℬ)) ∧ (rc37_HallDoubled → rc18_CylBoxReflInter) ∧ (rc20_FamCylBoxResidue → ReimerWprobCore) := by
-- proof
  apply StatMech.Walls.rc55_reimer_nonproduct


-- created on 2026-10-23
