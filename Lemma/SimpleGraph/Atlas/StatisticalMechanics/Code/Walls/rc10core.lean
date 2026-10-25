import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc10core.Part4
open Finset StatMech StatMech.Walls


/--
[rc10_occursOn_iff_fin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc10core.lean)
-/
@[path]
private lemma rc10_occursOn_iff_fin_eq
  [Fintype α]
  [DecidableEq α]
  {A : Set (ConfigSpace α)}
  {K : Finset α}
  {ω : ConfigSpace α}
-- given
  (hA : IsIncreasing A)
  (hK : K ⊆ cfgSupport ω) :
-- imply
  OccursOn A (↑K) ω ↔ supportCfg K ∈ A := by
-- proof
  apply StatMech.Walls.rc10_occursOn_iff_fin hA K ω hK

/--
[rc10_occursOn_restrict_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc10core.lean)
-/
@[path]
private lemma rc10_occursOn_restrict_mem_eq
  [Fintype α]
  [DecidableEq α]
  {A : Set (ConfigSpace α)}
  {Kset : Set α}
  {ω : ConfigSpace α}
-- given
  (h : OccursOn A Kset ω) :
-- imply
  supportCfg (cfgSupport ω ∩ {a | a ∈ Kset}.toFinset) ∈ A := by
-- proof
  apply StatMech.Walls.rc10_occursOn_restrict_mem Kset ω h

/--
[rc10_box_increasing_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc10core.lean)
-/
@[path]
private lemma rc10_box_increasing_iff_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
  {ω : ConfigSpace α}
-- given
  (hA : IsIncreasing A)
  (hB : IsIncreasing B) :
-- imply
  ω ∈ disjointOccurrence A B ↔ ∃ K L : Finset α, Disjoint K L ∧ K ⊆ cfgSupport ω ∧ L ⊆ cfgSupport ω ∧ supportCfg K ∈ A ∧ supportCfg L ∈ B := by
-- proof
  apply StatMech.Walls.rc10_box_increasing_iff hA hB ω

/--
[rc10_cfgSupport_compl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc10core.lean)
-/
@[path]
private lemma rc10_cfgSupport_compl_eq
  [Fintype α]
  [DecidableEq α]
  {ω : ConfigSpace α} :
-- imply
  cfgSupport (rmr_compl ω) = (cfgSupport ω)ᶜ := by
-- proof
  apply StatMech.Walls.rc10_cfgSupport_compl ω

/--
[rc10_isUpperSet_eventFamily](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc10core.lean)
-/
@[path]
private lemma rc10_isUpperSet_eventFamily_eq
  [Fintype α]
  [DecidableEq α]
  {A : Set (ConfigSpace α)}
-- given
  (hA : IsIncreasing A) :
-- imply
  IsUpperSet ((eventFamily A) : Set (Finset α)) := by
-- proof
  apply StatMech.Walls.rc10_isUpperSet_eventFamily hA

/--
[rc10_eventFamily_familyEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc10core.lean)
-/
@[path]
private lemma rc10_eventFamily_familyEvent_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 : Finset (Finset α)} :
-- imply
  eventFamily (familyEvent 𝒜) = 𝒜 := by
-- proof
  apply StatMech.Walls.rc10_eventFamily_familyEvent 𝒜

/--
[rc10_card_via_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc10core.lean)
-/
@[path]
private lemma rc10_card_via_support_eq
  [Fintype α]
  [DecidableEq α]
  [DecidablePred P]
  [DecidablePred Q]
-- given
  (P : Finset α → Prop)
  (Q : ConfigSpace α → Prop)
  (h : ∀ ω, Q ω ↔ P (cfgSupport ω)) :
-- imply
  #(univ.filter Q) = #(univ.filter P) := by
-- proof
  apply StatMech.Walls.rc10_card_via_support P Q h

/--
[rc10_card_box_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc10core.lean)
-/
@[path]
private lemma rc10_card_box_eq_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
-- given
  (hA : IsIncreasing A)
  (hB : IsIncreasing B) :
-- imply
  #(univ.filter (fun ω : ConfigSpace α => ω ∈ disjointOccurrence A B)) = #(rc10_boxSupp (eventFamily A) (eventFamily B)) := by
-- proof
  apply StatMech.Walls.rc10_card_box_eq A B hA hB

/--
[rc10_mem_iff_eventFamily](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc10core.lean)
-/
@[path]
private lemma rc10_mem_iff_eventFamily_eq
  [Fintype α]
  [DecidableEq α]
  {A : Set (ConfigSpace α)}
  {ω : ConfigSpace α} :
-- imply
  ω ∈ A ↔ cfgSupport ω ∈ eventFamily A := by
-- proof
  apply StatMech.Walls.rc10_mem_iff_eventFamily A ω

/--
[rc10_card_reflInter_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc10core.lean)
-/
@[path]
private lemma rc10_card_reflInter_eq_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)} :
-- imply
  #(univ.filter (fun ω : ConfigSpace α => ω ∈ A ∩ rmr_reflect B)) = #(rc10_reflInter (eventFamily A) (eventFamily B)) := by
-- proof
  apply StatMech.Walls.rc10_card_reflInter_eq A B

/--
[rc10_deficit_incInc_of_bkr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc10core.lean)
-/
@[path]
private lemma rc10_deficit_incInc_of_bkr_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {A B : Set (ConfigSpace (Fin n))}
-- given
  (h : rc10_BKRSetFamily)
  (hA : IsIncreasing A)
  (hB : IsIncreasing B) :
-- imply
  rc5_deficit A B ≤ 0 := by
-- proof
  apply StatMech.Walls.rc10_deficit_incInc_of_bkr h hA hB

/--
[rc10_deficitIncInc_of_bkr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc10core.lean)
-/
@[path]
private lemma rc10_deficitIncInc_of_bkr_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : rc10_BKRSetFamily) :
-- imply
  rc10_DeficitBridgeIncInc := by
-- proof
  apply StatMech.Walls.rc10_deficitIncInc_of_bkr h

/--
[rc10_bkr_of_deficitIncInc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc10core.lean)
-/
@[path]
private lemma rc10_bkr_of_deficitIncInc_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : rc10_DeficitBridgeIncInc) :
-- imply
  rc10_BKRSetFamily := by
-- proof
  apply StatMech.Walls.rc10_bkr_of_deficitIncInc h

/--
[rc10_bkr_iff_deficitIncInc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc10core.lean)
-/
@[path]
private lemma rc10_bkr_iff_deficitIncInc_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc10_BKRSetFamily ↔ rc10_DeficitBridgeIncInc := by
-- proof
  apply StatMech.Walls.rc10_bkr_iff_deficitIncInc

/--
[rc10_deficitIncInc_of_deficitBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc10core.lean)
-/
@[path]
private lemma rc10_deficitIncInc_of_deficitBridge_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : rc7_DeficitBridge) :
-- imply
  rc10_DeficitBridgeIncInc := by
-- proof
  apply StatMech.Walls.rc10_deficitIncInc_of_deficitBridge h

/--
[rc10_deficitBridge_iff_incInc_and_nonmono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc10core.lean)
-/
@[path]
private lemma rc10_deficitBridge_iff_incInc_and_nonmono_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc7_DeficitBridge ↔ (rc10_DeficitBridgeIncInc ∧ ∀ (n : ℕ) (A B : Set (ConfigSpace (Fin n))), (¬ IsIncreasing A ∧ ¬ IsDecreasing A) ∨ (¬ IsIncreasing B ∧ ¬ IsDecreasing B) → rc5_deficit A B ≤ 0) := by
-- proof
  apply StatMech.Walls.rc10_deficitBridge_iff_incInc_and_nonmono

/--
[rc10_ad_product_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc10core.lean)
-/
@[path]
private lemma rc10_ad_product_bound_eq
  [Fintype α]
  [DecidableEq α]
  [DecidableEq β]
  {𝒜 ℬ : Finset (Finset β)} :
-- imply
  #𝒜 * #ℬ ≤ #(𝒜 ⊼ ℬ) * #(𝒜 ⊻ ℬ) := by
-- proof
  apply StatMech.Walls.rc10_ad_product_bound 𝒜 ℬ

/--
[rc10_deficit_incInc_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc10core.lean)
-/
@[path]
private lemma rc10_deficit_incInc_one_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace (Fin 1))}
  {_ : IsIncreasing A}
  {_ : IsIncreasing B} :
-- imply
  rc5_deficit A B ≤ 0 := by
-- proof
  apply StatMech.Walls.rc10_deficit_incInc_one A B _ _

/--
[rc10_boxSupp_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc10core.lean)
-/
@[path]
private lemma rc10_boxSupp_univ_eq
  [Fintype α]
  [DecidableEq α]
  [Fintype β]
  [DecidableEq β] :
-- imply
  rc10_boxSupp (univ : Finset (Finset β)) univ = univ := by
-- proof
  apply StatMech.Walls.rc10_boxSupp_univ

/--
[rc10_cardform_setfamily_reduction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc10core.lean)
-/
@[path]
private lemma rc10_cardform_setfamily_reduction_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (rc10_BKRSetFamily ↔ rc10_DeficitBridgeIncInc) ∧ (rc7_DeficitBridge → rc10_DeficitBridgeIncInc) ∧ (rc7_DeficitBridge ↔ (rc10_DeficitBridgeIncInc ∧ ∀ (n : ℕ) (A B : Set (ConfigSpace (Fin n))), (¬ IsIncreasing A ∧ ¬ IsDecreasing A) ∨ (¬ IsIncreasing B ∧ ¬ IsDecreasing B) → rc5_deficit A B ≤ 0)) := by
-- proof
  apply StatMech.Walls.rc10_cardform_setfamily_reduction


-- created on 2026-10-23
