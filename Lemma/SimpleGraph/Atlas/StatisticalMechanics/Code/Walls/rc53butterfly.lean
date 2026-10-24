import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.rc53butterfly
open Finset StatMech StatMech.Walls


/--
[rc53_boxWithWitness_eq_famCylBoxDoubled](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc53butterfly.lean)
-/
@[path]
private lemma rc53_boxWithWitness_eq_famCylBoxDoubled_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  rc53_boxWithWitness 𝒜 ℬ = rc46_famCylBoxDoubled 𝒜 ℬ := by
-- proof
  apply StatMech.Walls.rc53_boxWithWitness_eq_famCylBoxDoubled 𝒜 ℬ

/--
[rc53_boxWithWitness_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc53butterfly.lean)
-/
@[path]
private lemma rc53_boxWithWitness_card_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  (rc53_boxWithWitness 𝒜 ℬ).card = (rc20_famCylBox 𝒜 ℬ).card := by
-- proof
  apply StatMech.Walls.rc53_boxWithWitness_card 𝒜 ℬ

/--
[rc53_dbl_compl_isCubeFilling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc53butterfly.lean)
-/
@[path]
private lemma rc53_dbl_compl_isCubeFilling_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {R : Finset (Fin n)} :
-- imply
  rc53_isCubeFilling (dbl R Rᶜ) := by
-- proof
  apply StatMech.Walls.rc53_dbl_compl_isCubeFilling R

/--
[rc53_boxWithWitness_all_cubeFilling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc53butterfly.lean)
-/
@[path]
private lemma rc53_boxWithWitness_all_cubeFilling_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {U : Finset (Fin n ⊕ Fin n)}
-- given
  (hU : U ∈ rc53_boxWithWitness 𝒜 ℬ) :
-- imply
  rc53_isCubeFilling U := by
-- proof
  apply StatMech.Walls.rc53_boxWithWitness_all_cubeFilling 𝒜 ℬ hU

/--
[rc53_cubeFillCount_boxWithWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc53butterfly.lean)
-/
@[path]
private lemma rc53_cubeFillCount_boxWithWitness_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))} :
-- imply
  rc53_cubeFillCount (rc53_boxWithWitness 𝒜 ℬ) = (rc20_famCylBox 𝒜 ℬ).card := by
-- proof
  apply StatMech.Walls.rc53_cubeFillCount_boxWithWitness 𝒜 ℬ

/--
[rc53_doubleCompress_boxWithWitness_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc53butterfly.lean)
-/
@[path]
private lemma rc53_doubleCompress_boxWithWitness_card_eq
  [Fintype α]
  [DecidableEq α]
  {i : α}
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  (doubleCompress i (rc53_boxWithWitness 𝒜 ℬ)).card = (rc53_boxWithWitness 𝒜 ℬ).card := by
-- proof
  apply StatMech.Walls.rc53_doubleCompress_boxWithWitness_card i 𝒜 ℬ

/--
[rc53_boxWithWitness_eq_comp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc53butterfly.lean)
-/
@[path]
private lemma rc53_boxWithWitness_eq_comp_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))} :
-- imply
  rc53_boxWithWitness 𝒜 ℬ = (rc20_famCylBoxComp n 𝒜 ℬ).image (fun S => dbl S Sᶜ) := by
-- proof
  apply StatMech.Walls.rc53_boxWithWitness_eq_comp n 𝒜 ℬ

/--
[rc53_cubeFillCount_eq_comp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc53butterfly.lean)
-/
@[path]
private lemma rc53_cubeFillCount_eq_comp_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {F : Finset (Finset (Fin n ⊕ Fin n))} :
-- imply
  rc53_cubeFillCount F = (F.filter (fun U => decide ((univ.filter (fun i => Sum.inl i ∈ U)) = (univ.filter (fun i => Sum.inr i ∈ U))ᶜ) = true)).card := by
-- proof
  apply StatMech.Walls.rc53_cubeFillCount_eq_comp F

/--
[rc53_cubeFillCount_strictly_decreases_fin3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc53butterfly.lean)
-/
@[path]
private lemma rc53_cubeFillCount_strictly_decreases_fin3_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc53_cubeFillCount (doubleCompress 1 (rc53_boxWithWitness rc46_Adn rc46_Bdn)) < rc53_cubeFillCount (rc53_boxWithWitness rc46_Adn rc46_Bdn) := by
-- proof
  apply StatMech.Walls.rc53_cubeFillCount_strictly_decreases_fin3

/--
[rc53_boxMonotonisation_functional_refuted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc53butterfly.lean)
-/
@[path]
private lemma rc53_boxMonotonisation_functional_refuted_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  ∃ (𝒜 ℬ : Finset (Finset (Fin 3))) (i : Fin 3), rc53_cubeFillCount (doubleCompress i (rc53_boxWithWitness 𝒜 ℬ)) < rc53_cubeFillCount (rc53_boxWithWitness 𝒜 ℬ) := by
-- proof
  apply StatMech.Walls.rc53_boxMonotonisation_functional_refuted

/--
[rc53_cubeFillCount_le_reflInter_at_increasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc53butterfly.lean)
-/
@[path]
private lemma rc53_cubeFillCount_le_reflInter_at_increasing_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {A B : Set (ConfigSpace (Fin n))}
-- given
  (hA : IsIncreasing A)
  (hB : IsIncreasing B) :
-- imply
  rc53_cubeFillCount (rc53_boxWithWitness (eventFamily A) (eventFamily B)) ≤ (rc10_reflInter (eventFamily A) (eventFamily B)).card := by
-- proof
  apply StatMech.Walls.rc53_cubeFillCount_le_reflInter_at_increasing hA hB

/--
[rc53_doubleCompress_dpairsCount_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc53butterfly.lean)
-/
@[path]
private lemma rc53_doubleCompress_dpairsCount_invariant_eq
  [Fintype α]
  [DecidableEq α]
  {i : α}
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  (doubleCompress i (boxDoubled 𝒜 ℬ)).card = (boxDoubled 𝒜 ℬ).card := by
-- proof
  apply StatMech.Walls.rc53_doubleCompress_dpairsCount_invariant i 𝒜 ℬ

/--
[rc53_dpairsCount_wrong_side](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc53butterfly.lean)
-/
@[path]
private lemma rc53_dpairsCount_wrong_side_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  (rc10_reflInter 𝒜 ℬ).card ≤ (boxDoubled 𝒜 ℬ).card := by
-- proof
  apply StatMech.Walls.rc53_dpairsCount_wrong_side 𝒜 ℬ

/--
[rc53_reimer_of_hallDoubled](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc53butterfly.lean)
-/
@[path]
private lemma rc53_reimer_of_hallDoubled_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : rc37_HallDoubled) :
-- imply
  rc18_CylBoxReflInter := by
-- proof
  apply StatMech.Walls.rc53_reimer_of_hallDoubled h

/--
[rc53_famCylBoxResidue_of_hallDoubled](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc53butterfly.lean)
-/
@[path]
private lemma rc53_famCylBoxResidue_of_hallDoubled_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : rc37_HallDoubled) :
-- imply
  rc20_FamCylBoxResidue := by
-- proof
  apply StatMech.Walls.rc53_famCylBoxResidue_of_hallDoubled h

/--
[rc53_wall_holds_on_refuter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc53butterfly.lean)
-/
@[path]
private lemma rc53_wall_holds_on_refuter_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (rc20_famCylBoxComp 3 rc46_Adn rc46_Bdn).card ≤ (rc20_reflInterComp 3 rc46_Adn rc46_Bdn).card := by
-- proof
  apply StatMech.Walls.rc53_wall_holds_on_refuter

/--
[rc53_reimer_boxWithWitness_refuted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc53butterfly.lean)
-/
@[path]
private lemma rc53_reimer_boxWithWitness_refuted_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (∀ (𝒜 ℬ : Finset (Finset (Fin 3))), rc53_cubeFillCount (rc53_boxWithWitness 𝒜 ℬ) = (rc20_famCylBox 𝒜 ℬ).card) ∧ (∀ (i : Fin 3) (𝒜 ℬ : Finset (Finset (Fin 3))), (doubleCompress i (rc53_boxWithWitness 𝒜 ℬ)).card = (rc53_boxWithWitness 𝒜 ℬ).card) ∧ (∃ (𝒜 ℬ : Finset (Finset (Fin 3))) (i : Fin 3), rc53_cubeFillCount (doubleCompress i (rc53_boxWithWitness 𝒜 ℬ)) < rc53_cubeFillCount (rc53_boxWithWitness 𝒜 ℬ)) ∧ (∀ (𝒜 ℬ : Finset (Finset (Fin 3))), (rc10_reflInter 𝒜 ℬ).card ≤ (boxDoubled 𝒜 ℬ).card) ∧ (rc37_HallDoubled → rc18_CylBoxReflInter) ∧ ((rc20_famCylBoxComp 3 rc46_Adn rc46_Bdn).card ≤ (rc20_reflInterComp 3 rc46_Adn rc46_Bdn).card) := by
-- proof
  apply StatMech.Walls.rc53_reimer_boxWithWitness_refuted


-- created on 2026-10-23
