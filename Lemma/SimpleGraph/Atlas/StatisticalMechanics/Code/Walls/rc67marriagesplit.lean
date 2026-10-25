import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc67marriagesplit.Part3
open Finset StatMech StatMech.Walls


/--
[rc67_self_mem_nbhd_of_box_reflInter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc67marriagesplit.lean)
-/
@[path]
private lemma rc67_self_mem_nbhd_of_box_reflInter_eq
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {S : Finset (Fin n)}
-- given
  (hbox : S ∈ rc20_famCylBox 𝒜 ℬ)
  (hRI : S ∈ rc10_reflInter 𝒜 ℬ) :
-- imply
  S ∈ rc59_nbhd 𝒜 ℬ S := by
-- proof
  apply StatMech.Walls.rc67_self_mem_nbhd_of_box_reflInter 𝒜 ℬ hbox hRI

/--
[rc67_Tin_self_subset_biUnion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc67marriagesplit.lean)
-/
@[path]
private lemma rc67_Tin_self_subset_biUnion_eq
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {T : Finset (Finset (Fin n))}
-- given
  (hbox : ∀ S ∈ T, S ∈ rc20_famCylBox 𝒜 ℬ)
  (hRI : ∀ S ∈ T, S ∈ rc10_reflInter 𝒜 ℬ) :
-- imply
  T ⊆ T.biUnion (rc59_nbhd 𝒜 ℬ) := by
-- proof
  apply StatMech.Walls.rc67_Tin_self_subset_biUnion 𝒜 ℬ hbox hRI

/--
[rc67_marriage_of_subset_reflInter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc67marriagesplit.lean)
-/
@[path]
private lemma rc67_marriage_of_subset_reflInter_eq
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {T : Finset (Finset (Fin n))}
-- given
  (hbox : ∀ S ∈ T, S ∈ rc20_famCylBox 𝒜 ℬ)
  (hRI : ∀ S ∈ T, S ∈ rc10_reflInter 𝒜 ℬ) :
-- imply
  T.card ≤ (T.biUnion (rc59_nbhd 𝒜 ℬ)).card := by
-- proof
  apply StatMech.Walls.rc67_marriage_of_subset_reflInter 𝒜 ℬ hbox hRI

/--
[rc67_split_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc67marriagesplit.lean)
-/
@[path]
private lemma rc67_split_card_eq
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {T : Finset (Finset (Fin n))} :
-- imply
  T.card = (rc67_Tin 𝒜 ℬ T).card + (rc67_Toff 𝒜 ℬ T).card := by
-- proof
  apply StatMech.Walls.rc67_split_card 𝒜 ℬ T

/--
[rc67_Tin_subset_biUnion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc67marriagesplit.lean)
-/
@[path]
private lemma rc67_Tin_subset_biUnion_eq
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {T : Finset (Finset (Fin n))}
-- given
  (hbox : ∀ S ∈ T, S ∈ rc20_famCylBox 𝒜 ℬ) :
-- imply
  rc67_Tin 𝒜 ℬ T ⊆ T.biUnion (rc59_nbhd 𝒜 ℬ) := by
-- proof
  apply StatMech.Walls.rc67_Tin_subset_biUnion 𝒜 ℬ hbox

/--
[rc67_marriage_of_forcedSelfMatch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc67marriagesplit.lean)
-/
@[path]
private lemma rc67_marriage_of_forcedSelfMatch_eq
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {T : Finset (Finset (Fin n))}
  {g : Finset (Fin n) → Finset (Fin n)}
-- given
  (hbox : ∀ S ∈ T, S ∈ rc20_famCylBox 𝒜 ℬ)
  (hg : rc67_ForcedSelfMatchSDR 𝒜 ℬ T g) :
-- imply
  T.card ≤ (T.biUnion (rc59_nbhd 𝒜 ℬ)).card := by
-- proof
  apply StatMech.Walls.rc67_marriage_of_forcedSelfMatch 𝒜 ℬ hbox hg

/--
[rc67_witness_empty_mem_reflInter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc67marriagesplit.lean)
-/
@[path]
private lemma rc67_witness_empty_mem_reflInter_eq
  {n : ℕ} :
-- imply
  (∅ : Finset (Fin 2)) ∈ rc10_reflInter rc66_wA rc66_wB := by
-- proof
  apply StatMech.Walls.rc67_witness_empty_mem_reflInter

/--
[rc67_witness_empty_mem_Tin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc67marriagesplit.lean)
-/
@[path]
private lemma rc67_witness_empty_mem_Tin_eq
  {n : ℕ} :
-- imply
  (∅ : Finset (Fin 2)) ∈ rc67_Tin rc66_wA rc66_wB {∅, {0}} := by
-- proof
  apply StatMech.Walls.rc67_witness_empty_mem_Tin

/--
[rc67_witness_singleton_mem_Toff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc67marriagesplit.lean)
-/
@[path]
private lemma rc67_witness_singleton_mem_Toff_eq
  {n : ℕ} :
-- imply
  ({0} : Finset (Fin 2)) ∈ rc67_Toff rc66_wA rc66_wB {∅, {0}} := by
-- proof
  apply StatMech.Walls.rc67_witness_singleton_mem_Toff

/--
[rc67_forcedSelfMatch_fails_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc67marriagesplit.lean)
-/
@[path]
private lemma rc67_forcedSelfMatch_fails_witness_eq
  {n : ℕ} :
-- imply
  ¬ ∃ g : Finset (Fin 2) → Finset (Fin 2), rc67_ForcedSelfMatchSDR rc66_wA rc66_wB {∅, {0}} g := by
-- proof
  apply StatMech.Walls.rc67_forcedSelfMatch_fails_witness

/--
[rc67_witness_marriage_holds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc67marriagesplit.lean)
-/
@[path]
private lemma rc67_witness_marriage_holds_eq
  {n : ℕ} :
-- imply
  ({∅, {0}} : Finset (Finset (Fin 2))).card ≤ (({∅, {0}} : Finset (Finset (Fin 2))).biUnion (rc59_nbhd rc66_wA rc66_wB)).card := by
-- proof
  apply StatMech.Walls.rc67_witness_marriage_holds

/--
[rc67_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc67marriagesplit.lean)
-/
@[path]
private lemma rc67_status_eq
  {n : ℕ} :
-- imply
  (∀ (m : ℕ) (𝒜 ℬ : Finset (Finset (Fin m))) (T : Finset (Finset (Fin m))), (∀ S ∈ T, S ∈ rc20_famCylBox 𝒜 ℬ) → (∀ S ∈ T, S ∈ rc10_reflInter 𝒜 ℬ) → T.card ≤ (T.biUnion (rc59_nbhd 𝒜 ℬ)).card) ∧ (∀ (m : ℕ) (𝒜 ℬ : Finset (Finset (Fin m))) (T : Finset (Finset (Fin m))), (∀ S ∈ T, S ∈ rc20_famCylBox 𝒜 ℬ) → (∃ g : Finset (Fin m) → Finset (Fin m), rc67_ForcedSelfMatchSDR 𝒜 ℬ T g) → T.card ≤ (T.biUnion (rc59_nbhd 𝒜 ℬ)).card) ∧ (¬ ∃ g : Finset (Fin 2) → Finset (Fin 2), rc67_ForcedSelfMatchSDR rc66_wA rc66_wB {∅, {0}} g) ∧ (({∅, {0}} : Finset (Finset (Fin 2))).card ≤ (({∅, {0}} : Finset (Finset (Fin 2))).biUnion (rc59_nbhd rc66_wA rc66_wB)).card) := by
-- proof
  apply StatMech.Walls.rc67_status


-- created on 2026-10-23
