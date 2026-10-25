import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc58bipartiteflow.Part4
open Finset StatMech StatMech.Walls


/--
[rc58_box_mono_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc58bipartiteflow.lean)
-/
@[path]
private lemma rc58_box_mono_card_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (rc20_famCylBoxComp 2 rc58_Amono rc58_Bmono).card = 2 := by
-- proof
  apply StatMech.Walls.rc58_box_mono_card

/--
[rc58_box_mono_compressed_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc58bipartiteflow.lean)
-/
@[path]
private lemma rc58_box_mono_compressed_card_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (rc20_famCylBoxComp 2 (Down.compression 0 rc58_Amono) (Down.compression 0 rc58_Bmono)).card = 1 := by
-- proof
  apply StatMech.Walls.rc58_box_mono_compressed_card

/--
[rc58_box_strict_shrink](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc58bipartiteflow.lean)
-/
@[path]
private lemma rc58_box_strict_shrink_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (rc20_famCylBoxComp 2 (Down.compression 0 rc58_Amono) (Down.compression 0 rc58_Bmono)).card < (rc20_famCylBoxComp 2 rc58_Amono rc58_Bmono).card := by
-- proof
  apply StatMech.Walls.rc58_box_strict_shrink

/--
[rc58_boxCompressionMono_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc58bipartiteflow.lean)
-/
@[path]
private lemma rc58_boxCompressionMono_false_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  ¬ rc22_BoxCompressionMono := by
-- proof
  apply StatMech.Walls.rc58_boxCompressionMono_false

/--
[rc58_wall_holds_on_monoCE](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc58bipartiteflow.lean)
-/
@[path]
private lemma rc58_wall_holds_on_monoCE_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (rc20_famCylBoxComp 2 rc58_Amono rc58_Bmono).card ≤ (rc20_reflInterComp 2 rc58_Amono rc58_Bmono).card := by
-- proof
  apply StatMech.Walls.rc58_wall_holds_on_monoCE

/--
[rc58_matching_iff_wall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc58bipartiteflow.lean)
-/
@[path]
private lemma rc58_matching_iff_wall_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) ↔ Nonempty ((rc20_famCylBox 𝒜 ℬ : Finset (Finset α)) ↪ (rc10_reflInter 𝒜 ℬ : Finset (Finset α))) := by
-- proof
  apply StatMech.Walls.rc58_matching_iff_wall 𝒜 ℬ

/--
[rc58_kadm_subset_reflInter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc58bipartiteflow.lean)
-/
@[path]
private lemma rc58_kadm_subset_reflInter_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {S : Finset (Fin n)} :
-- imply
  rc58_kadm n 𝒜 ℬ S ⊆ rc10_reflInter 𝒜 ℬ := by
-- proof
  apply StatMech.Walls.rc58_kadm_subset_reflInter n 𝒜 ℬ S

/--
[rc58_kadmSDR_closes_wall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc58bipartiteflow.lean)
-/
@[path]
private lemma rc58_kadmSDR_closes_wall_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : rc58_KadmSDR) :
-- imply
  rc20_FamCylBoxResidue := by
-- proof
  apply StatMech.Walls.rc58_kadmSDR_closes_wall h

/--
[rc58_reimer_closes_of_kadmSDR](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc58bipartiteflow.lean)
-/
@[path]
private lemma rc58_reimer_closes_of_kadmSDR_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : rc58_KadmSDR) :
-- imply
  rc18_CylBoxReflInter := by
-- proof
  apply StatMech.Walls.rc58_reimer_closes_of_kadmSDR h

/--
[rc58_kadm_hall_iff_sdr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc58bipartiteflow.lean)
-/
@[path]
private lemma rc58_kadm_hall_iff_sdr_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))} :
-- imply
  (∀ 𝒮 : Finset (rc20_famCylBox 𝒜 ℬ), #𝒮 ≤ #(𝒮.biUnion (fun S => rc58_kadm n 𝒜 ℬ (S : Finset (Fin n))))) ↔ ∃ f : (rc20_famCylBox 𝒜 ℬ) → Finset (Fin n), Function.Injective f ∧ ∀ S : (rc20_famCylBox 𝒜 ℬ), f S ∈ rc58_kadm n 𝒜 ℬ (S : Finset (Fin n)) := by
-- proof
  apply StatMech.Walls.rc58_kadm_hall_iff_sdr n 𝒜 ℬ

/--
[rc58_kadm_hall_holds_on_rc57pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc58bipartiteflow.lean)
-/
@[path]
private lemma rc58_kadm_hall_holds_on_rc57pair_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  ∀ 𝒯 ∈ (rc20_famCylBoxComp 2 rc58_Arc57 rc58_Brc57).powerset, 𝒯.card ≤ (𝒯.biUnion (rc58_kadm 2 rc58_Arc57 rc58_Brc57)).card := by
-- proof
  apply StatMech.Walls.rc58_kadm_hall_holds_on_rc57pair

/--
[rc58_kadm_proper_on_rc57pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc58bipartiteflow.lean)
-/
@[path]
private lemma rc58_kadm_proper_on_rc57pair_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (rc58_kadm 2 rc58_Arc57 rc58_Brc57 {0}).card < (rc20_reflInterComp 2 rc58_Arc57 rc58_Brc57).card := by
-- proof
  apply StatMech.Walls.rc58_kadm_proper_on_rc57pair

/--
[rc58_reimer_bipartiteFlow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc58bipartiteflow.lean)
-/
@[path]
private lemma rc58_reimer_bipartiteFlow_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (¬ rc22_BoxCompressionMono) ∧ ((rc20_famCylBoxComp 2 rc58_Amono rc58_Bmono).card ≤ (rc20_reflInterComp 2 rc58_Amono rc58_Bmono).card) ∧ (∀ (𝒜 ℬ : Finset (Finset (Fin 2))), #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) ↔ Nonempty ((rc20_famCylBox 𝒜 ℬ : Finset (Finset (Fin 2))) ↪ (rc10_reflInter 𝒜 ℬ : Finset (Finset (Fin 2))))) ∧ (∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) (S : Finset (Fin n)), rc58_kadm n 𝒜 ℬ S ⊆ rc10_reflInter 𝒜 ℬ) ∧ (rc58_KadmSDR → rc18_CylBoxReflInter) ∧ (∀ 𝒯 ∈ (rc20_famCylBoxComp 2 rc58_Arc57 rc58_Brc57).powerset, 𝒯.card ≤ (𝒯.biUnion (rc58_kadm 2 rc58_Arc57 rc58_Brc57)).card) ∧ ((rc58_kadm 2 rc58_Arc57 rc58_Brc57 {0}).card < (rc20_reflInterComp 2 rc58_Arc57 rc58_Brc57).card) := by
-- proof
  apply StatMech.Walls.rc58_reimer_bipartiteFlow


-- created on 2026-10-23
