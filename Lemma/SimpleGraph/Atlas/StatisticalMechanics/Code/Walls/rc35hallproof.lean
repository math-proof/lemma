import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc35hallproof.Part3
open Finset StatMech StatMech.Walls


/--
[rc35_slice_subset_admOneSidedA](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc35hallproof.lean)
-/
@[path]
private lemma rc35_slice_subset_admOneSidedA_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {S K : Finset (Fin n)}
-- given
  (hKA : ∀ T : Finset (Fin n), T ∩ K = S ∩ K → T ∈ 𝒜) :
-- imply
  rc35_traceSlice 𝒜 ℬ K S ⊆ rc33_admOneSidedA n 𝒜 ℬ S := by
-- proof
  apply StatMech.Walls.rc35_slice_subset_admOneSidedA n 𝒜 ℬ hKA

/--
[rc35_admOneSidedA_eq_biUnion_slice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc35hallproof.lean)
-/
@[path]
private lemma rc35_admOneSidedA_eq_biUnion_slice_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {S : Finset (Fin n)} :
-- imply
  rc33_admOneSidedA n 𝒜 ℬ S = (rc35_awitsA n 𝒜 S).biUnion (fun K => rc35_traceSlice 𝒜 ℬ K S) := by
-- proof
  apply StatMech.Walls.rc35_admOneSidedA_eq_biUnion_slice n 𝒜 ℬ S

/--
[rc35_hallOneSidedA_iff_injection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc35hallproof.lean)
-/
@[path]
private lemma rc35_hallOneSidedA_iff_injection_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))} :
-- imply
  (∀ 𝒯 ∈ (rc20_famCylBox 𝒜 ℬ).powerset, 𝒯.card ≤ (𝒯.biUnion (rc33_admOneSidedA n 𝒜 ℬ)).card) ↔ ∃ f : Finset (Fin n) → Finset (Fin n), Set.InjOn f (rc20_famCylBox 𝒜 ℬ : Set (Finset (Fin n))) ∧ ∀ S ∈ rc20_famCylBox 𝒜 ℬ, f S ∈ rc33_admOneSidedA n 𝒜 ℬ S := by
-- proof
  apply StatMech.Walls.rc35_hallOneSidedA_iff_injection n 𝒜 ℬ

/--
[rc35_oneSidedInjection_iff_hallOneSidedA](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc35hallproof.lean)
-/
@[path]
private lemma rc35_oneSidedInjection_iff_hallOneSidedA_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc35_OneSidedInjection ↔ rc33_HallOneSidedA := by
-- proof
  apply StatMech.Walls.rc35_oneSidedInjection_iff_hallOneSidedA

/--
[rc35_famCylBoxResidue_of_oneSidedInjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc35hallproof.lean)
-/
@[path]
private lemma rc35_famCylBoxResidue_of_oneSidedInjection_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : rc35_OneSidedInjection) :
-- imply
  rc20_FamCylBoxResidue := by
-- proof
  apply StatMech.Walls.rc35_famCylBoxResidue_of_oneSidedInjection h

/--
[rc35_reimer_closes_of_oneSidedInjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc35hallproof.lean)
-/
@[path]
private lemma rc35_reimer_closes_of_oneSidedInjection_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : rc35_OneSidedInjection) :
-- imply
  rc18_CylBoxReflInter := by
-- proof
  apply StatMech.Walls.rc35_reimer_closes_of_oneSidedInjection h

/--
[rc35_oneSidedInjection_fin2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc35hallproof.lean)
-/
@[path]
private lemma rc35_oneSidedInjection_fin2_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset (Fin 2))} :
-- imply
  ∃ f : Finset (Fin 2) → Finset (Fin 2), Set.InjOn f (rc20_famCylBox 𝒜 ℬ : Set (Finset (Fin 2))) ∧ ∀ S ∈ rc20_famCylBox 𝒜 ℬ, f S ∈ rc33_admOneSidedA 2 𝒜 ℬ S := by
-- proof
  apply StatMech.Walls.rc35_oneSidedInjection_fin2 𝒜 ℬ

/--
[rc35_oneSidedInjection_fin3_refuter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc35hallproof.lean)
-/
@[path]
private lemma rc35_oneSidedInjection_fin3_refuter_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  ∃ f : Finset (Fin 3) → Finset (Fin 3), Set.InjOn f (rc20_famCylBox rc32_A3 rc32_B3 : Set (Finset (Fin 3))) ∧ ∀ S ∈ rc20_famCylBox rc32_A3 rc32_B3, f S ∈ rc33_admOneSidedA 3 rc32_A3 rc32_B3 S := by
-- proof
  apply StatMech.Walls.rc35_oneSidedInjection_fin3_refuter

/--
[rc35_box_not_subset_reflInter_fin2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc35hallproof.lean)
-/
@[path]
private lemma rc35_box_not_subset_reflInter_fin2_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  ¬ (rc20_famCylBox ({∅, {0}} : Finset (Finset (Fin 2))) ({∅, {1}}) ⊆ rc10_reflInter ({∅, {0}}) ({∅, {1}})) := by
-- proof
  apply StatMech.Walls.rc35_box_not_subset_reflInter_fin2

/--
[rc35_self_not_admissible_fin2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc35hallproof.lean)
-/
@[path]
private lemma rc35_self_not_admissible_fin2_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (∅ : Finset (Fin 2)) ∉ rc33_admOneSidedA 2 ({∅, {0}}) ({∅, {1}}) ∅ := by
-- proof
  apply StatMech.Walls.rc35_self_not_admissible_fin2

/--
[rc35_minNeighbour_lt_box_fin2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc35hallproof.lean)
-/
@[path]
private lemma rc35_minNeighbour_lt_box_fin2_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (rc33_admOneSidedA 2 ({∅, {0}, {1}}) ({∅, {0}, {1}, {0, 1}}) {0}).card < (rc20_famCylBox ({∅, {0}, {1}} : Finset (Finset (Fin 2))) ({∅, {0}, {1}, {0, 1}})).card := by
-- proof
  apply StatMech.Walls.rc35_minNeighbour_lt_box_fin2

/--
[rc35_hallOneSidedA_holds_minWitness_fin2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc35hallproof.lean)
-/
@[path]
private lemma rc35_hallOneSidedA_holds_minWitness_fin2_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc33_hallOneSidedA 2 ({∅, {0}, {1}}) ({∅, {0}, {1}, {0, 1}}) = true := by
-- proof
  apply StatMech.Walls.rc35_hallOneSidedA_holds_minWitness_fin2

/--
[rc35_reimer_hallconcrete](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc35hallproof.lean)
-/
@[path]
private lemma rc35_reimer_hallconcrete_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (rc35_OneSidedInjection ↔ rc33_HallOneSidedA) ∧ (rc35_OneSidedInjection → rc18_CylBoxReflInter) ∧ (∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) (S K : Finset (Fin n)), (∀ T : Finset (Fin n), T ∩ K = S ∩ K → T ∈ 𝒜) → rc35_traceSlice 𝒜 ℬ K S ⊆ rc33_admOneSidedA n 𝒜 ℬ S) ∧ (¬ (rc20_famCylBox ({∅, {0}} : Finset (Finset (Fin 2))) ({∅, {1}}) ⊆ rc10_reflInter ({∅, {0}}) ({∅, {1}}))) ∧ ((rc33_admOneSidedA 2 ({∅, {0}, {1}}) ({∅, {0}, {1}, {0, 1}}) {0}).card < (rc20_famCylBox ({∅, {0}, {1}} : Finset (Finset (Fin 2))) ({∅, {0}, {1}, {0, 1}})).card) ∧ (rc33_hallOneSidedA 2 ({∅, {0}, {1}}) ({∅, {0}, {1}, {0, 1}}) = true) := by
-- proof
  apply StatMech.Walls.rc35_reimer_hallconcrete


-- created on 2026-10-23
