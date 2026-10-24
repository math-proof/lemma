import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.rc34butterfly
open Finset StatMech StatMech.Walls


/--
[rc34_reflInter_symmDiff_mem_admOneSidedA](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc34butterfly.lean)
-/
@[path]
private lemma rc34_reflInter_symmDiff_mem_admOneSidedA_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {S K L : Finset (Fin n)}
-- given
  (hKL : Disjoint K L)
  (hKA : ∀ T : Finset (Fin n), T ∩ K = S ∩ K → T ∈ 𝒜)
  (hLB : ∀ T : Finset (Fin n), T ∩ L = S ∩ L → T ∈ ℬ) :
-- imply
  symmDiff S L ∈ rc33_admOneSidedA n 𝒜 ℬ S := by
-- proof
  apply StatMech.Walls.rc34_reflInter_symmDiff_mem_admOneSidedA n 𝒜 ℬ hKL hKA hLB

/--
[rc34_self_mem_admOneSidedA](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc34butterfly.lean)
-/
@[path]
private lemma rc34_self_mem_admOneSidedA_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {S K : Finset (Fin n)}
-- given
  (hSRI : S ∈ rc10_reflInter 𝒜 ℬ)
  (hKA : ∀ T : Finset (Fin n), T ∩ K = S ∩ K → T ∈ 𝒜) :
-- imply
  S ∈ rc33_admOneSidedA n 𝒜 ℬ S := by
-- proof
  apply StatMech.Walls.rc34_self_mem_admOneSidedA n 𝒜 ℬ hSRI hKA

/--
[rc34_admComp_subset_admOneSidedA](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc34butterfly.lean)
-/
@[path]
private lemma rc34_admComp_subset_admOneSidedA_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {S : Finset (Fin n)} :
-- imply
  rc21_admComp n 𝒜 ℬ S ⊆ rc33_admOneSidedA n 𝒜 ℬ S := by
-- proof
  apply StatMech.Walls.rc34_admComp_subset_admOneSidedA n 𝒜 ℬ S

/--
[rc34_hall_of_subgraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc34butterfly.lean)
-/
@[path]
private lemma rc34_hall_of_subgraph_eq
  [Fintype α]
  [DecidableEq α]
  [DecidableEq β]
  {𝒢 : Finset (Finset β)}
  {t t' : Finset β → Finset (Finset β)}
-- given
  (hsub : ∀ S ∈ 𝒢, t S ⊆ t' S)
  (hHall : ∀ 𝒯 ∈ 𝒢.powerset, 𝒯.card ≤ (𝒯.biUnion t).card) :
-- imply
  ∀ 𝒯 ∈ 𝒢.powerset, 𝒯.card ≤ (𝒯.biUnion t').card := by
-- proof
  apply StatMech.Walls.rc34_hall_of_subgraph 𝒢 t t' hsub hHall

/--
[rc34_hallOneSidedA_of_localReflHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc34butterfly.lean)
-/
@[path]
private lemma rc34_hallOneSidedA_of_localReflHall_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
-- given
  (hHall : ∀ 𝒯 ∈ (rc20_famCylBox 𝒜 ℬ).powerset, 𝒯.card ≤ (𝒯.biUnion (rc21_admComp n 𝒜 ℬ)).card) :
-- imply
  ∀ 𝒯 ∈ (rc20_famCylBox 𝒜 ℬ).powerset, 𝒯.card ≤ (𝒯.biUnion (rc33_admOneSidedA n 𝒜 ℬ)).card := by
-- proof
  apply StatMech.Walls.rc34_hallOneSidedA_of_localReflHall n 𝒜 ℬ hHall

/--
[rc34_card_boxDoubled_A3B3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc34butterfly.lean)
-/
@[path]
private lemma rc34_card_boxDoubled_A3B3_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (boxDoubled rc34_A3 rc34_B3).card = 2 := by
-- proof
  apply StatMech.Walls.rc34_card_boxDoubled_A3B3

/--
[rc34_card_boxDoubled_compressed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc34butterfly.lean)
-/
@[path]
private lemma rc34_card_boxDoubled_compressed_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (boxDoubled (Down.compression 0 rc34_A3) (UV.compression {0} ∅ rc34_B3)).card = 4 := by
-- proof
  apply StatMech.Walls.rc34_card_boxDoubled_compressed

/--
[rc34_doubleCompress_ne_componentBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc34butterfly.lean)
-/
@[path]
private lemma rc34_doubleCompress_ne_componentBox_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  doubleCompress 0 (boxDoubled rc34_A3 rc34_B3) ≠ boxDoubled (Down.compression 0 rc34_A3) (UV.compression {0} ∅ rc34_B3) := by
-- proof
  apply StatMech.Walls.rc34_doubleCompress_ne_componentBox

/--
[rc34_localReflHall_prop_of_bool](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc34butterfly.lean)
-/
@[path]
private lemma rc34_localReflHall_prop_of_bool_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
-- given
  (h : rc21_localReflSearch n 𝒜 ℬ = true) :
-- imply
  ∀ 𝒯 ∈ (rc20_famCylBox 𝒜 ℬ).powerset, 𝒯.card ≤ (𝒯.biUnion (rc21_admComp n 𝒜 ℬ)).card := by
-- proof
  apply StatMech.Walls.rc34_localReflHall_prop_of_bool n 𝒜 ℬ h

/--
[rc34_localReflSearch_fin1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc34butterfly.lean)
-/
@[path]
private lemma rc34_localReflSearch_fin1_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset (Fin 1))} :
-- imply
  rc21_localReflSearch 1 𝒜 ℬ = true := by
-- proof
  apply StatMech.Walls.rc34_localReflSearch_fin1 𝒜 ℬ

/--
[rc34_wall_fin1_via_subgraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc34butterfly.lean)
-/
@[path]
private lemma rc34_wall_fin1_via_subgraph_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset (Fin 1))} :
-- imply
  #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) := by
-- proof
  apply StatMech.Walls.rc34_wall_fin1_via_subgraph 𝒜 ℬ

/--
[rc34_reimer_butterfly](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc34butterfly.lean)
-/
@[path]
private lemma rc34_reimer_butterfly_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) (S : Finset (Fin n)), rc21_admComp n 𝒜 ℬ S ⊆ rc33_admOneSidedA n 𝒜 ℬ S) ∧ (∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))), (∀ 𝒯 ∈ (rc20_famCylBox 𝒜 ℬ).powerset, 𝒯.card ≤ (𝒯.biUnion (rc21_admComp n 𝒜 ℬ)).card) → (∀ 𝒯 ∈ (rc20_famCylBox 𝒜 ℬ).powerset, 𝒯.card ≤ (𝒯.biUnion (rc33_admOneSidedA n 𝒜 ℬ)).card)) ∧ (∀ (𝒜 ℬ : Finset (Finset (Fin 1))), #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ)) ∧ (doubleCompress 0 (boxDoubled rc34_A3 rc34_B3) ≠ boxDoubled (Down.compression 0 rc34_A3) (UV.compression {0} ∅ rc34_B3)) := by
-- proof
  apply StatMech.Walls.rc34_reimer_butterfly


-- created on 2026-10-23
