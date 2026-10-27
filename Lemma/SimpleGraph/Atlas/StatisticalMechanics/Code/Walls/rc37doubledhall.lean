import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc37doubledhall.Part4
open Finset StatMech StatMech.Walls


/--
[rc37_admOneSidedA_eq_inter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc37doubledhall.lean)
-/
@[path]
private lemma rc37_admOneSidedA_eq_inter_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {S : Finset (Fin n)} :
-- imply
  rc33_admOneSidedA n 𝒜 ℬ S = rc37_admLeft n 𝒜 S ∩ rc37_rightMem n ℬ := by
-- proof
  apply StatMech.Walls.rc37_admOneSidedA_eq_inter n 𝒜 ℬ S

/--
[rc37_rightMem_indep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc37doubledhall.lean)
-/
@[path]
private lemma rc37_rightMem_indep_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {S S' : Finset (Fin n)} :
-- imply
  ∃ RM : Finset (Finset (Fin n)), rc33_admOneSidedA n 𝒜 ℬ S = rc37_admLeft n 𝒜 S ∩ RM ∧ rc33_admOneSidedA n 𝒜 ℬ S' = rc37_admLeft n 𝒜 S' ∩ RM := by
-- proof
  apply StatMech.Walls.rc37_rightMem_indep n 𝒜 ℬ S S'

/--
[rc37_dblCompl_mem_boxDoubled](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc37doubledhall.lean)
-/
@[path]
private lemma rc37_dblCompl_mem_boxDoubled_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {R : Finset α}
-- given
  (hR : R ∈ rc10_reflInter 𝒜 ℬ) :
-- imply
  dbl R Rᶜ ∈ boxDoubled 𝒜 ℬ := by
-- proof
  apply StatMech.Walls.rc37_dblCompl_mem_boxDoubled 𝒜 ℬ hR

/--
[rc37_dblCompl_injOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc37doubledhall.lean)
-/
@[path]
private lemma rc37_dblCompl_injOn_eq
  [Fintype α]
  [DecidableEq α]
  {s : Set (Finset α)} :
-- imply
  Set.InjOn (fun R : Finset α => dbl R Rᶜ) s := by
-- proof
  apply StatMech.Walls.rc37_dblCompl_injOn s

/--
[rc37_complBoxDoubled_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc37doubledhall.lean)
-/
@[path]
private lemma rc37_complBoxDoubled_subset_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  rc37_complBoxDoubled 𝒜 ℬ ⊆ boxDoubled 𝒜 ℬ := by
-- proof
  apply StatMech.Walls.rc37_complBoxDoubled_subset 𝒜 ℬ

/--
[rc37_complBoxDoubled_card_eq_reflInter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc37doubledhall.lean)
-/
@[path]
private lemma rc37_complBoxDoubled_card_eq_reflInter_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  (rc37_complBoxDoubled 𝒜 ℬ).card = (rc10_reflInter 𝒜 ℬ).card := by
-- proof
  apply StatMech.Walls.rc37_complBoxDoubled_card_eq_reflInter 𝒜 ℬ

/--
[rc37_admDoubled_subset_boxDoubled](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc37doubledhall.lean)
-/
@[path]
private lemma rc37_admDoubled_subset_boxDoubled_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {S : Finset (Fin n)} :
-- imply
  rc37_admDoubled n 𝒜 ℬ S ⊆ boxDoubled 𝒜 ℬ := by
-- proof
  apply StatMech.Walls.rc37_admDoubled_subset_boxDoubled n 𝒜 ℬ S

/--
[rc37_biUnion_admDoubled_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc37doubledhall.lean)
-/
@[path]
private lemma rc37_biUnion_admDoubled_card_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {𝒯 : Finset (Finset (Fin n))} :
-- imply
  (𝒯.biUnion (rc37_admDoubled n 𝒜 ℬ)).card = (𝒯.biUnion (rc33_admOneSidedA n 𝒜 ℬ)).card := by
-- proof
  apply StatMech.Walls.rc37_biUnion_admDoubled_card n 𝒜 ℬ 𝒯

/--
[rc37_hallDoubled_iff_hallOneSidedA](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc37doubledhall.lean)
-/
@[path]
private lemma rc37_hallDoubled_iff_hallOneSidedA_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc37_HallDoubled ↔ rc33_HallOneSidedA := by
-- proof
  apply StatMech.Walls.rc37_hallDoubled_iff_hallOneSidedA

/--
[rc37_famCylBoxResidue_of_hallDoubled](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc37doubledhall.lean)
-/
@[path]
private lemma rc37_famCylBoxResidue_of_hallDoubled_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : rc37_HallDoubled) :
-- imply
  rc20_FamCylBoxResidue := by
-- proof
  apply StatMech.Walls.rc37_famCylBoxResidue_of_hallDoubled h

/--
[rc37_reimer_closes_of_hallDoubled](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc37doubledhall.lean)
-/
@[path]
private lemma rc37_reimer_closes_of_hallDoubled_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : rc37_HallDoubled) :
-- imply
  rc18_CylBoxReflInter := by
-- proof
  apply StatMech.Walls.rc37_reimer_closes_of_hallDoubled h

/--
[rc37_hallDoubled_fin2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc37doubledhall.lean)
-/
@[path]
private lemma rc37_hallDoubled_fin2_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset (Fin 2))} :
-- imply
  ∀ 𝒯 ∈ (rc20_famCylBox 𝒜 ℬ).powerset, 𝒯.card ≤ (𝒯.biUnion (rc37_admDoubled 2 𝒜 ℬ)).card := by
-- proof
  apply StatMech.Walls.rc37_hallDoubled_fin2 𝒜 ℬ

/--
[rc37_hallDoubled_fin3_refuter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc37doubledhall.lean)
-/
@[path]
private lemma rc37_hallDoubled_fin3_refuter_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  ∀ 𝒯 ∈ (rc20_famCylBox rc32_A3 rc32_B3).powerset, 𝒯.card ≤ (𝒯.biUnion (rc37_admDoubled 3 rc32_A3 rc32_B3)).card := by
-- proof
  apply StatMech.Walls.rc37_hallDoubled_fin3_refuter

/--
[rc37_admDoubled_proper_fin3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc37doubledhall.lean)
-/
@[path]
private lemma rc37_admDoubled_proper_fin3_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (rc37_admDoubled 3 rc32_A3 rc32_B3 {1}).card < (boxDoubled rc32_A3 rc32_B3).card := by
-- proof
  apply StatMech.Walls.rc37_admDoubled_proper_fin3

/--
[rc37_reimer_doubledhall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc37doubledhall.lean)
-/
@[path]
private lemma rc37_reimer_doubledhall_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) (S : Finset (Fin n)), rc33_admOneSidedA n 𝒜 ℬ S = rc37_admLeft n 𝒜 S ∩ rc37_rightMem n ℬ) ∧ (∀ (𝒜 ℬ : Finset (Finset (Fin 3))), (rc37_complBoxDoubled 𝒜 ℬ).card = (rc10_reflInter 𝒜 ℬ).card ∧ rc37_complBoxDoubled 𝒜 ℬ ⊆ boxDoubled 𝒜 ℬ) ∧ (rc37_HallDoubled ↔ rc33_HallOneSidedA) ∧ (rc37_HallDoubled → rc18_CylBoxReflInter) ∧ (∀ 𝒯 ∈ (rc20_famCylBox rc32_A3 rc32_B3).powerset, 𝒯.card ≤ (𝒯.biUnion (rc37_admDoubled 3 rc32_A3 rc32_B3)).card) ∧ ((rc37_admDoubled 3 rc32_A3 rc32_B3 {1}).card < (boxDoubled rc32_A3 rc32_B3).card) := by
-- proof
  apply StatMech.Walls.rc37_reimer_doubledhall


-- created on 2026-10-23
