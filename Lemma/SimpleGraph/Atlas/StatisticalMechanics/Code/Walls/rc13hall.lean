import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc13hall.Part4
open Finset StatMech StatMech.Walls


/--
[rc13_mem_adm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc13hall.lean)
-/
@[path]
private lemma rc13_mem_adm_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {S R : Finset α} :
-- imply
  R ∈ rc13_adm 𝒜 ℬ S ↔ ∃ T ⊆ S, T ∈ 𝒜 ∧ S \ T ∈ ℬ ∧ T ⊆ R ∧ Disjoint R (S \ T) := by
-- proof
  apply StatMech.Walls.rc13_mem_adm 𝒜 ℬ S R

/--
[rc13_adm_subset_reflInter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc13hall.lean)
-/
@[path]
private lemma rc13_adm_subset_reflInter_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {S : Finset α}
-- given
  (h𝒜 : IsUpperSet (𝒜 : Set (Finset α)))
  (hℬ : IsUpperSet (ℬ : Set (Finset α))) :
-- imply
  rc13_adm 𝒜 ℬ S ⊆ rc10_reflInter 𝒜 ℬ := by
-- proof
  apply StatMech.Walls.rc13_adm_subset_reflInter 𝒜 ℬ h𝒜 hℬ S

/--
[rc13_marriage_iff_subtype](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc13hall.lean)
-/
@[path]
private lemma rc13_marriage_iff_subtype_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  rc13_MarriageCondition 𝒜 ℬ ↔ ∀ s : Finset (rc10_boxSupp 𝒜 ℬ), #s ≤ #(s.biUnion (fun x => rc13_adm 𝒜 ℬ x.val)) := by
-- proof
  apply StatMech.Walls.rc13_marriage_iff_subtype 𝒜 ℬ

/--
[rc13_hall_abstract](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc13hall.lean)
-/
@[path]
private lemma rc13_hall_abstract_eq
  [Fintype α]
  [DecidableEq α]
  {t : ι → Finset (Finset α)} :
-- imply
  (∀ s : Finset ι, #s ≤ #(s.biUnion t)) ↔ ∃ g : ι → Finset α, Function.Injective g ∧ ∀ x, g x ∈ t x := by
-- proof
  apply StatMech.Walls.rc13_hall_abstract t

/--
[rc13_marriage_iff_transversal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc13hall.lean)
-/
@[path]
private lemma rc13_marriage_iff_transversal_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  rc13_MarriageCondition 𝒜 ℬ ↔ ∃ g : rc10_boxSupp 𝒜 ℬ → Finset α, Function.Injective g ∧ ∀ x, g x ∈ rc13_adm 𝒜 ℬ x.val := by
-- proof
  apply StatMech.Walls.rc13_marriage_iff_transversal 𝒜 ℬ

/--
[rc13_transversal_of_reflectionInjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc13hall.lean)
-/
@[path]
private lemma rc13_transversal_of_reflectionInjection_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
-- given
  (h : rc12_ReimerReflectionInjection 𝒜 ℬ) :
-- imply
  ∃ g : rc10_boxSupp 𝒜 ℬ → Finset α, Function.Injective g ∧ ∀ x, g x ∈ rc13_adm 𝒜 ℬ x.val := by
-- proof
  apply StatMech.Walls.rc13_transversal_of_reflectionInjection 𝒜 ℬ h

/--
[rc13_reflectionInjection_of_transversal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc13hall.lean)
-/
@[path]
private lemma rc13_reflectionInjection_of_transversal_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
-- given
  (h : ∃ g : rc10_boxSupp 𝒜 ℬ → Finset α, Function.Injective g ∧ ∀ x, g x ∈ rc13_adm 𝒜 ℬ x.val) :
-- imply
  rc12_ReimerReflectionInjection 𝒜 ℬ := by
-- proof
  apply StatMech.Walls.rc13_reflectionInjection_of_transversal 𝒜 ℬ h

/--
[rc13_marriage_iff_reflectionInjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc13hall.lean)
-/
@[path]
private lemma rc13_marriage_iff_reflectionInjection_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  rc13_MarriageCondition 𝒜 ℬ ↔ rc12_ReimerReflectionInjection 𝒜 ℬ := by
-- proof
  apply StatMech.Walls.rc13_marriage_iff_reflectionInjection 𝒜 ℬ

/--
[rc13_marriage_imp_bkrInjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc13hall.lean)
-/
@[path]
private lemma rc13_marriage_imp_bkrInjection_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
-- given
  (h𝒜 : IsUpperSet (𝒜 : Set (Finset α)))
  (hℬ : IsUpperSet (ℬ : Set (Finset α)))
  (h : rc13_MarriageCondition 𝒜 ℬ) :
-- imply
  rc11_BKRInjection 𝒜 ℬ := by
-- proof
  apply StatMech.Walls.rc13_marriage_imp_bkrInjection 𝒜 ℬ h𝒜 hℬ h

/--
[rc13_marriage_imp_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc13hall.lean)
-/
@[path]
private lemma rc13_marriage_imp_card_le_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
-- given
  (h𝒜 : IsUpperSet (𝒜 : Set (Finset α)))
  (hℬ : IsUpperSet (ℬ : Set (Finset α)))
  (h : rc13_MarriageCondition 𝒜 ℬ) :
-- imply
  #(rc10_boxSupp 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) := by
-- proof
  apply StatMech.Walls.rc13_marriage_imp_card_le 𝒜 ℬ h𝒜 hℬ h

/--
[rc13_marriage_iff_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc13hall.lean)
-/
@[path]
private lemma rc13_marriage_iff_card_le_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
-- given
  (h𝒜 : IsUpperSet (𝒜 : Set (Finset α)))
  (hℬ : IsUpperSet (ℬ : Set (Finset α))) :
-- imply
  rc13_MarriageCondition 𝒜 ℬ ↔ (rc12_ReimerReflectionInjection 𝒜 ℬ ∧ #(rc10_boxSupp 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ)) := by
-- proof
  apply StatMech.Walls.rc13_marriage_iff_card_le 𝒜 ℬ h𝒜 hℬ

/--
[rc13_biUnion_adm_subset_reflInter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc13hall.lean)
-/
@[path]
private lemma rc13_biUnion_adm_subset_reflInter_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
-- given
  (h𝒜 : IsUpperSet (𝒜 : Set (Finset α)))
  (hℬ : IsUpperSet (ℬ : Set (Finset α))) :
-- imply
  (rc10_boxSupp 𝒜 ℬ).biUnion (rc13_adm 𝒜 ℬ) ⊆ rc10_reflInter 𝒜 ℬ := by
-- proof
  apply StatMech.Walls.rc13_biUnion_adm_subset_reflInter 𝒜 ℬ h𝒜 hℬ

/--
[rc13_marriageFull_imp_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc13hall.lean)
-/
@[path]
private lemma rc13_marriageFull_imp_card_le_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
-- given
  (h𝒜 : IsUpperSet (𝒜 : Set (Finset α)))
  (hℬ : IsUpperSet (ℬ : Set (Finset α)))
  (h : #(rc10_boxSupp 𝒜 ℬ) ≤ #((rc10_boxSupp 𝒜 ℬ).biUnion (rc13_adm 𝒜 ℬ))) :
-- imply
  #(rc10_boxSupp 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) := by
-- proof
  apply StatMech.Walls.rc13_marriageFull_imp_card_le 𝒜 ℬ h𝒜 hℬ h

/--
[rc13_admComp_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc13hall.lean)
-/
@[path]
private lemma rc13_admComp_eq_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {S : Finset α} :
-- imply
  rc13_admComp 𝒜 ℬ S = rc13_adm 𝒜 ℬ S := by
-- proof
  apply StatMech.Walls.rc13_admComp_eq 𝒜 ℬ S

/--
[rc13_marriageSearch_iff_marriage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc13hall.lean)
-/
@[path]
private lemma rc13_marriageSearch_iff_marriage_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset (Fin 2))} :
-- imply
  rc13_marriageSearch 𝒜 ℬ = true ↔ rc13_MarriageCondition 𝒜 ℬ := by
-- proof
  apply StatMech.Walls.rc13_marriageSearch_iff_marriage 𝒜 ℬ

/--
[rc13_marriageSearch_iff_card_fin2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc13hall.lean)
-/
@[path]
private lemma rc13_marriageSearch_iff_card_fin2_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  ∀ 𝒜 ℬ : Finset (Finset (Fin 2)), rc12_isUpperFin 2 𝒜 → rc12_isUpperFin 2 ℬ → (rc13_marriageSearch 𝒜 ℬ = true ↔ (rc12_boxSuppComp 𝒜 ℬ).card ≤ (rc12_reflInterComp 𝒜 ℬ).card) := by
-- proof
  apply StatMech.Walls.rc13_marriageSearch_iff_card_fin2

/--
[rc13_marriageSearch_fin2_holds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc13hall.lean)
-/
@[path]
private lemma rc13_marriageSearch_fin2_holds_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  ∀ 𝒜 ℬ : Finset (Finset (Fin 2)), rc12_isUpperFin 2 𝒜 → rc12_isUpperFin 2 ℬ → rc13_marriageSearch 𝒜 ℬ = true := by
-- proof
  apply StatMech.Walls.rc13_marriageSearch_fin2_holds

/--
[rc13_hall_route_is_circular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc13hall.lean)
-/
@[path]
private lemma rc13_hall_route_is_circular_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (∀ 𝒜 ℬ : Finset (Finset α), rc13_MarriageCondition 𝒜 ℬ ↔ rc12_ReimerReflectionInjection 𝒜 ℬ) ∧ (∀ 𝒜 ℬ : Finset (Finset α), rc13_MarriageCondition 𝒜 ℬ ↔ ∃ g : rc10_boxSupp 𝒜 ℬ → Finset α, Function.Injective g ∧ ∀ x, g x ∈ rc13_adm 𝒜 ℬ x.val) ∧ (∀ 𝒜 ℬ : Finset (Finset (Fin 2)), rc12_isUpperFin 2 𝒜 → rc12_isUpperFin 2 ℬ → (rc13_marriageSearch 𝒜 ℬ = true ↔ (rc12_boxSuppComp 𝒜 ℬ).card ≤ (rc12_reflInterComp 𝒜 ℬ).card)) := by
-- proof
  apply StatMech.Walls.rc13_hall_route_is_circular


-- created on 2026-10-23
