import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc68countmarriage.Part3
open Finset StatMech StatMech.Walls


/--
[rc68_Tin_subset_biUnion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc68countmarriage.lean)
-/
@[path]
private lemma rc68_Tin_subset_biUnion_eq
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {T : Finset (Finset (Fin n))}
-- given
  (hbox : ∀ S ∈ T, S ∈ rc20_famCylBox 𝒜 ℬ) :
-- imply
  rc67_Tin 𝒜 ℬ T ⊆ T.biUnion (rc59_nbhd 𝒜 ℬ) := by
-- proof
  apply StatMech.Walls.rc68_Tin_subset_biUnion 𝒜 ℬ hbox

/--
[rc68_biUnion_card_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc68countmarriage.lean)
-/
@[path]
private lemma rc68_biUnion_card_split_eq
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {T : Finset (Finset (Fin n))}
-- given
  (hbox : ∀ S ∈ T, S ∈ rc20_famCylBox 𝒜 ℬ) :
-- imply
  (T.biUnion (rc59_nbhd 𝒜 ℬ)).card = ((T.biUnion (rc59_nbhd 𝒜 ℬ)) \ rc67_Tin 𝒜 ℬ T).card + (rc67_Tin 𝒜 ℬ T).card := by
-- proof
  apply StatMech.Walls.rc68_biUnion_card_split 𝒜 ℬ hbox

/--
[rc68_marriage_of_countForm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc68countmarriage.lean)
-/
@[path]
private lemma rc68_marriage_of_countForm_eq
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {T : Finset (Finset (Fin n))}
-- given
  (hbox : ∀ S ∈ T, S ∈ rc20_famCylBox 𝒜 ℬ)
  (hcount : rc68_CountForm 𝒜 ℬ T) :
-- imply
  T.card ≤ (T.biUnion (rc59_nbhd 𝒜 ℬ)).card := by
-- proof
  apply StatMech.Walls.rc68_marriage_of_countForm 𝒜 ℬ hbox hcount

/--
[rc68_countForm_of_marriage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc68countmarriage.lean)
-/
@[path]
private lemma rc68_countForm_of_marriage_eq
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {T : Finset (Finset (Fin n))}
-- given
  (hbox : ∀ S ∈ T, S ∈ rc20_famCylBox 𝒜 ℬ)
  (hmar : T.card ≤ (T.biUnion (rc59_nbhd 𝒜 ℬ)).card) :
-- imply
  rc68_CountForm 𝒜 ℬ T := by
-- proof
  apply StatMech.Walls.rc68_countForm_of_marriage 𝒜 ℬ hbox hmar

/--
[rc68_countForm_iff_marriage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc68countmarriage.lean)
-/
@[path]
private lemma rc68_countForm_iff_marriage_eq
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {T : Finset (Finset (Fin n))}
-- given
  (hbox : ∀ S ∈ T, S ∈ rc20_famCylBox 𝒜 ℬ) :
-- imply
  rc68_CountForm 𝒜 ℬ T ↔ T.card ≤ (T.biUnion (rc59_nbhd 𝒜 ℬ)).card := by
-- proof
  apply StatMech.Walls.rc68_countForm_iff_marriage 𝒜 ℬ hbox

/--
[rc68_witness_Tin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc68countmarriage.lean)
-/
@[path]
private lemma rc68_witness_Tin_eq
  {n : ℕ} :
-- imply
  rc67_Tin rc66_wA rc66_wB {∅, {0}} = ({∅} : Finset (Finset (Fin 2))) := by
-- proof
  apply StatMech.Walls.rc68_witness_Tin

/--
[rc68_witness_Toff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc68countmarriage.lean)
-/
@[path]
private lemma rc68_witness_Toff_eq
  {n : ℕ} :
-- imply
  rc67_Toff rc66_wA rc66_wB {∅, {0}} = ({{0}} : Finset (Finset (Fin 2))) := by
-- proof
  apply StatMech.Walls.rc68_witness_Toff

/--
[rc68_witness_biUnion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc68countmarriage.lean)
-/
@[path]
private lemma rc68_witness_biUnion_eq
  {n : ℕ} :
-- imply
  ({∅, {0}} : Finset (Finset (Fin 2))).biUnion (rc59_nbhd rc66_wA rc66_wB) = ({∅, {1}} : Finset (Finset (Fin 2))) := by
-- proof
  apply StatMech.Walls.rc68_witness_biUnion

/--
[rc68_witness_countForm_holds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc68countmarriage.lean)
-/
@[path]
private lemma rc68_witness_countForm_holds_eq
  {n : ℕ} :
-- imply
  rc68_CountForm rc66_wA rc66_wB ({∅, {0}} : Finset (Finset (Fin 2))) := by
-- proof
  apply StatMech.Walls.rc68_witness_countForm_holds

/--
[rc68_witness_marriage_via_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc68countmarriage.lean)
-/
@[path]
private lemma rc68_witness_marriage_via_count_eq
  {n : ℕ} :
-- imply
  ({∅, {0}} : Finset (Finset (Fin 2))).card ≤ (({∅, {0}} : Finset (Finset (Fin 2))).biUnion (rc59_nbhd rc66_wA rc66_wB)).card := by
-- proof
  apply StatMech.Walls.rc68_witness_marriage_via_count

/--
[rc68_countFormLeaf_iff_indepHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc68countmarriage.lean)
-/
@[path]
private lemma rc68_countFormLeaf_iff_indepHall_eq
  {n : ℕ} :
-- imply
  rc68_CountFormLeaf ↔ rc59_IndepHall := by
-- proof
  apply StatMech.Walls.rc68_countFormLeaf_iff_indepHall

/--
[rc68_reimerWprobCore_of_countFormLeaf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc68countmarriage.lean)
-/
@[path]
private lemma rc68_reimerWprobCore_of_countFormLeaf_eq
  {n : ℕ}
-- given
  (h : rc68_CountFormLeaf) :
-- imply
  ReimerWprobCore := by
-- proof
  apply StatMech.Walls.rc68_reimerWprobCore_of_countFormLeaf h

/--
[rc68_countForm_fin2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc68countmarriage.lean)
-/
@[path]
private lemma rc68_countForm_fin2_eq
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin 2))}
  {T : Finset (Finset (Fin 2))}
-- given
  (hT : T ∈ (rc20_famCylBox 𝒜 ℬ).powerset) :
-- imply
  rc68_CountForm 𝒜 ℬ T := by
-- proof
  apply StatMech.Walls.rc68_countForm_fin2 𝒜 ℬ T hT

/--
[rc68_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc68countmarriage.lean)
-/
@[path]
private lemma rc68_status_eq
  {n : ℕ} :
-- imply
  (∀ (m : ℕ) (𝒜 ℬ : Finset (Finset (Fin m))) (T : Finset (Finset (Fin m))), (∀ S ∈ T, S ∈ rc20_famCylBox 𝒜 ℬ) → rc68_CountForm 𝒜 ℬ T → T.card ≤ (T.biUnion (rc59_nbhd 𝒜 ℬ)).card) ∧ (∀ (m : ℕ) (𝒜 ℬ : Finset (Finset (Fin m))) (T : Finset (Finset (Fin m))), (∀ S ∈ T, S ∈ rc20_famCylBox 𝒜 ℬ) → (rc68_CountForm 𝒜 ℬ T ↔ T.card ≤ (T.biUnion (rc59_nbhd 𝒜 ℬ)).card)) ∧ (rc68_CountFormLeaf ↔ rc59_IndepHall) ∧ (¬ ∃ g : Finset (Fin 2) → Finset (Fin 2), rc67_ForcedSelfMatchSDR rc66_wA rc66_wB {∅, {0}} g) ∧ rc68_CountForm rc66_wA rc66_wB ({∅, {0}} : Finset (Finset (Fin 2))) ∧ (rc68_CountFormLeaf → ReimerWprobCore) := by
-- proof
  apply StatMech.Walls.rc68_status


-- created on 2026-10-23
