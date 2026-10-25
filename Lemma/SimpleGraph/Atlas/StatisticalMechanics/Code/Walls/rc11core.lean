import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc11core.Part3
open Finset StatMech StatMech.Walls


/--
[rc11_boxSupp_upper_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc11core.lean)
-/
@[path]
private lemma rc11_boxSupp_upper_split_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {S : Finset α}
-- given
  (hℬ : IsUpperSet (ℬ : Set (Finset α))) :
-- imply
  S ∈ rc10_boxSupp 𝒜 ℬ ↔ ∃ T ⊆ S, T ∈ 𝒜 ∧ S \ T ∈ ℬ := by
-- proof
  apply StatMech.Walls.rc11_boxSupp_upper_split 𝒜 ℬ hℬ S

/--
[rc11_boxSupp_subset_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc11core.lean)
-/
@[path]
private lemma rc11_boxSupp_subset_left_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
-- given
  (h𝒜 : IsUpperSet (𝒜 : Set (Finset α))) :
-- imply
  rc10_boxSupp 𝒜 ℬ ⊆ 𝒜 := by
-- proof
  apply StatMech.Walls.rc11_boxSupp_subset_left 𝒜 ℬ h𝒜

/--
[rc11_boxSupp_subset_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc11core.lean)
-/
@[path]
private lemma rc11_boxSupp_subset_right_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
-- given
  (hℬ : IsUpperSet (ℬ : Set (Finset α))) :
-- imply
  rc10_boxSupp 𝒜 ℬ ⊆ ℬ := by
-- proof
  apply StatMech.Walls.rc11_boxSupp_subset_right 𝒜 ℬ hℬ

/--
[rc11_boxSupp_eq_reflInter_fin0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc11core.lean)
-/
@[path]
private lemma rc11_boxSupp_eq_reflInter_fin0_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset (Fin 0))} :
-- imply
  rc10_boxSupp 𝒜 ℬ = rc10_reflInter 𝒜 ℬ := by
-- proof
  apply StatMech.Walls.rc11_boxSupp_eq_reflInter_fin0 𝒜 ℬ

/--
[rc11_bkr_fin0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc11core.lean)
-/
@[path]
private lemma rc11_bkr_fin0_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset (Fin 0))}
-- given
  (_h𝒜 : IsUpperSet (𝒜 : Set (Finset (Fin 0))))
  (_hℬ : IsUpperSet (ℬ : Set (Finset (Fin 0)))) :
-- imply
  #(rc10_boxSupp 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) := by
-- proof
  apply StatMech.Walls.rc11_bkr_fin0 𝒜 ℬ _h𝒜 _hℬ

/--
[rc11_bkr_fin1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc11core.lean)
-/
@[path]
private lemma rc11_bkr_fin1_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset (Fin 1))}
-- given
  (h𝒜 : IsUpperSet (𝒜 : Set (Finset (Fin 1))))
  (hℬ : IsUpperSet (ℬ : Set (Finset (Fin 1)))) :
-- imply
  #(rc10_boxSupp 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) := by
-- proof
  apply StatMech.Walls.rc11_bkr_fin1 𝒜 ℬ h𝒜 hℬ

/--
[rc11_boxSupp_reflInter_right_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc11core.lean)
-/
@[path]
private lemma rc11_boxSupp_reflInter_right_univ_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 : Finset (Finset α)}
-- given
  (h𝒜 : IsUpperSet (𝒜 : Set (Finset α))) :
-- imply
  rc10_boxSupp 𝒜 univ = 𝒜 ∧ rc10_reflInter 𝒜 univ = 𝒜 := by
-- proof
  apply StatMech.Walls.rc11_boxSupp_reflInter_right_univ 𝒜 h𝒜

/--
[rc11_bkr_right_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc11core.lean)
-/
@[path]
private lemma rc11_bkr_right_univ_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 : Finset (Finset α)}
-- given
  (h𝒜 : IsUpperSet (𝒜 : Set (Finset α))) :
-- imply
  #(rc10_boxSupp 𝒜 univ) ≤ #(rc10_reflInter 𝒜 univ) := by
-- proof
  apply StatMech.Walls.rc11_bkr_right_univ 𝒜 h𝒜

/--
[rc11_boxSupp_left_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc11core.lean)
-/
@[path]
private lemma rc11_boxSupp_left_univ_eq
  [Fintype α]
  [DecidableEq α]
  {ℬ : Finset (Finset α)}
-- given
  (hℬ : IsUpperSet (ℬ : Set (Finset α))) :
-- imply
  rc10_boxSupp univ ℬ = ℬ := by
-- proof
  apply StatMech.Walls.rc11_boxSupp_left_univ ℬ hℬ

/--
[rc11_card_reflInter_left_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc11core.lean)
-/
@[path]
private lemma rc11_card_reflInter_left_univ_eq
  [Fintype α]
  [DecidableEq α]
  {ℬ : Finset (Finset α)} :
-- imply
  #(rc10_reflInter univ ℬ) = #ℬ := by
-- proof
  apply StatMech.Walls.rc11_card_reflInter_left_univ ℬ

/--
[rc11_bkr_left_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc11core.lean)
-/
@[path]
private lemma rc11_bkr_left_univ_eq
  [Fintype α]
  [DecidableEq α]
  {ℬ : Finset (Finset α)}
-- given
  (hℬ : IsUpperSet (ℬ : Set (Finset α))) :
-- imply
  #(rc10_boxSupp univ ℬ) ≤ #(rc10_reflInter univ ℬ) := by
-- proof
  apply StatMech.Walls.rc11_bkr_left_univ ℬ hℬ

/--
[rc11_card_le_of_injection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc11core.lean)
-/
@[path]
private lemma rc11_card_le_of_injection_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
-- given
  (h : rc11_BKRInjection 𝒜 ℬ) :
-- imply
  #(rc10_boxSupp 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) := by
-- proof
  apply StatMech.Walls.rc11_card_le_of_injection h

/--
[rc11_injection_of_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc11core.lean)
-/
@[path]
private lemma rc11_injection_of_card_le_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
-- given
  (h : #(rc10_boxSupp 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ)) :
-- imply
  rc11_BKRInjection 𝒜 ℬ := by
-- proof
  apply StatMech.Walls.rc11_injection_of_card_le h

/--
[rc11_injection_iff_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc11core.lean)
-/
@[path]
private lemma rc11_injection_iff_card_le_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  rc11_BKRInjection 𝒜 ℬ ↔ #(rc10_boxSupp 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) := by
-- proof
  apply StatMech.Walls.rc11_injection_iff_card_le 𝒜 ℬ

/--
[rc11_bkr_of_injectionAll](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc11core.lean)
-/
@[path]
private lemma rc11_bkr_of_injectionAll_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : rc11_BKRInjectionAll) :
-- imply
  rc10_BKRSetFamily := by
-- proof
  apply StatMech.Walls.rc11_bkr_of_injectionAll h

/--
[rc11_injectionAll_of_bkr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc11core.lean)
-/
@[path]
private lemma rc11_injectionAll_of_bkr_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : rc10_BKRSetFamily) :
-- imply
  rc11_BKRInjectionAll := by
-- proof
  apply StatMech.Walls.rc11_injectionAll_of_bkr h

/--
[rc11_BKRInjectionAll_iff_bkr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc11core.lean)
-/
@[path]
private lemma rc11_BKRInjectionAll_iff_bkr_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc11_BKRInjectionAll ↔ rc10_BKRSetFamily := by
-- proof
  apply StatMech.Walls.rc11_BKRInjectionAll_iff_bkr

/--
[rc11_boxSupp_not_downComp_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc11core.lean)
-/
@[path]
private lemma rc11_boxSupp_not_downComp_mono_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  ∃ 𝒜 : Finset (Finset (Fin 2)), #(rc10_boxSupp 𝒜 𝒜) < #(rc10_boxSupp (Down.compression 0 𝒜) (Down.compression 0 𝒜)) := by
-- proof
  apply StatMech.Walls.rc11_boxSupp_not_downComp_mono

/--
[rc11_bkr_false_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc11core.lean)
-/
@[path]
private lemma rc11_bkr_false_lower_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  ∃ 𝒜 : Finset (Finset (Fin 2)), IsLowerSet (𝒜 : Set (Finset (Fin 2))) ∧ #(rc10_reflInter 𝒜 𝒜) < #(rc10_boxSupp 𝒜 𝒜) := by
-- proof
  apply StatMech.Walls.rc11_bkr_false_lower

/--
[rc11_core_doubleCover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc11core.lean)
-/
@[path]
private lemma rc11_core_doubleCover_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {S : Finset α} :
-- imply
  S ∈ rc10_boxSupp 𝒜 ℬ ↔ ∃ U ∈ boxDoubled 𝒜 ℬ, U.image (Sum.elim id id) ⊆ S := by
-- proof
  apply StatMech.Walls.rc11_core_doubleCover 𝒜 ℬ S

/--
[rc11_core_compressionEngine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc11core.lean)
-/
@[path]
private lemma rc11_core_compressionEngine_eq
  [Fintype α]
  [DecidableEq α]
  [DecidableEq β]
  {𝒜 ℬ : Finset (Finset β)} :
-- imply
  ((boxDoubled 𝒜 ℬ).card = dpairsCount 𝒜 ℬ) ∧ (∀ i : β, dpairsCount 𝒜 ℬ ≤ dpairsCount (Down.compression i 𝒜) (Down.compression i ℬ)) ∧ (∀ i : β, (dpairsCount (Down.compression i 𝒜) (Down.compression i ℬ) : ℤ) - dpairsCount 𝒜 ℬ = (dpairsCount (𝒜.memberSubfamily i) (ℬ.memberSubfamily i) : ℤ) - dpairsCount (𝒜.memberSubfamily i ∩ 𝒜.nonMemberSubfamily i) (ℬ.memberSubfamily i ∩ ℬ.nonMemberSubfamily i)) ∧ (∀ cs : List β, (iterDownComp cs 𝒜).card = 𝒜.card) ∧ (∃ cs : List β, IsLowerSet ((iterDownComp cs 𝒜) : Set (Finset β)) ∧ dpairsCount 𝒜 ℬ ≤ dpairsCount (iterDownComp cs 𝒜) (iterDownComp cs ℬ)) ∧ (IsLowerSet (𝒜 : Set (Finset β)) → IsLowerSet (ℬ : Set (Finset β)) → ∀ i : β, dpairsCount (𝒜.memberSubfamily i) (ℬ.memberSubfamily i) ≤ dpairsCount (𝒜.nonMemberSubfamily i) (ℬ.nonMemberSubfamily i)) := by
-- proof
  apply StatMech.Walls.rc11_core_compressionEngine 𝒜 ℬ

/--
[rc11_injection_fin0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc11core.lean)
-/
@[path]
private lemma rc11_injection_fin0_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset (Fin 0))}
-- given
  (h𝒜 : IsUpperSet (𝒜 : Set (Finset (Fin 0))))
  (hℬ : IsUpperSet (ℬ : Set (Finset (Fin 0)))) :
-- imply
  rc11_BKRInjection 𝒜 ℬ := by
-- proof
  apply StatMech.Walls.rc11_injection_fin0 𝒜 ℬ h𝒜 hℬ

/--
[rc11_injection_fin1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc11core.lean)
-/
@[path]
private lemma rc11_injection_fin1_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset (Fin 1))}
-- given
  (h𝒜 : IsUpperSet (𝒜 : Set (Finset (Fin 1))))
  (hℬ : IsUpperSet (ℬ : Set (Finset (Fin 1)))) :
-- imply
  rc11_BKRInjection 𝒜 ℬ := by
-- proof
  apply StatMech.Walls.rc11_injection_fin1 𝒜 ℬ h𝒜 hℬ

/--
[rc11_core_bkr_setfamily](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc11core.lean)
-/
@[path]
private lemma rc11_core_bkr_setfamily_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (rc11_BKRInjectionAll ↔ rc10_BKRSetFamily) ∧ (rc10_BKRSetFamily ↔ rc10_DeficitBridgeIncInc) ∧ (∀ 𝒜 ℬ : Finset (Finset (Fin 0)), IsUpperSet (𝒜 : Set (Finset (Fin 0))) → IsUpperSet (ℬ : Set (Finset (Fin 0))) → #(rc10_boxSupp 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ)) ∧ (∀ 𝒜 ℬ : Finset (Finset (Fin 1)), IsUpperSet (𝒜 : Set (Finset (Fin 1))) → IsUpperSet (ℬ : Set (Finset (Fin 1))) → #(rc10_boxSupp 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ)) ∧ (∃ 𝒜 : Finset (Finset (Fin 2)), #(rc10_boxSupp 𝒜 𝒜) < #(rc10_boxSupp (Down.compression 0 𝒜) (Down.compression 0 𝒜))) := by
-- proof
  apply StatMech.Walls.rc11_core_bkr_setfamily


-- created on 2026-10-23
