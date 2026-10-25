import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc65marriagetwo.Part3
open Finset StatMech StatMech.Walls


/--
[rc65_nbhd_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc65marriagetwo.lean)
-/
@[path]
private lemma rc65_nbhd_nonempty_eq
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {S : Finset (Fin n)}
-- given
  (hS : S ∈ rc20_famCylBox 𝒜 ℬ) :
-- imply
  (rc59_nbhd 𝒜 ℬ S).Nonempty := by
-- proof
  apply StatMech.Walls.rc65_nbhd_nonempty 𝒜 ℬ hS

/--
[rc65_pair_biUnion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc65marriagetwo.lean)
-/
@[path]
private lemma rc65_pair_biUnion_eq
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {S₁ S₂ : Finset (Fin n)} :
-- imply
  ({S₁, S₂} : Finset (Finset (Fin n))).biUnion (rc59_nbhd 𝒜 ℬ) = rc59_nbhd 𝒜 ℬ S₁ ∪ rc59_nbhd 𝒜 ℬ S₂ := by
-- proof
  apply StatMech.Walls.rc65_pair_biUnion 𝒜 ℬ S₁ S₂

/--
[rc65_marriage_two_of_nbhd_card_ge_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc65marriagetwo.lean)
-/
@[path]
private lemma rc65_marriage_two_of_nbhd_card_ge_two_eq
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {S₁ S₂ : Finset (Fin n)}
-- given
  (h : 2 ≤ (rc59_nbhd 𝒜 ℬ S₁).card ∨ 2 ≤ (rc59_nbhd 𝒜 ℬ S₂).card) :
-- imply
  rc65_MarriageTwoPair 𝒜 ℬ S₁ S₂ := by
-- proof
  apply StatMech.Walls.rc65_marriage_two_of_nbhd_card_ge_two 𝒜 ℬ S₁ S₂ h

/--
[rc65_marriage_two_of_nbhd_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc65marriagetwo.lean)
-/
@[path]
private lemma rc65_marriage_two_of_nbhd_ne_eq
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {S₁ S₂ : Finset (Fin n)}
-- given
  (h0 : (rc59_nbhd 𝒜 ℬ S₁).Nonempty)
  (h1 : (rc59_nbhd 𝒜 ℬ S₂).Nonempty)
  (hne : rc59_nbhd 𝒜 ℬ S₁ ≠ rc59_nbhd 𝒜 ℬ S₂) :
-- imply
  rc65_MarriageTwoPair 𝒜 ℬ S₁ S₂ := by
-- proof
  apply StatMech.Walls.rc65_marriage_two_of_nbhd_ne 𝒜 ℬ h0 h1 hne

/--
[rc65_marriage_two_of_commonWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc65marriagetwo.lean)
-/
@[path]
private lemma rc65_marriage_two_of_commonWitness_eq
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {S₁ S₂ K : Finset (Fin n)}
-- given
  (hKA₁ : ∀ T : Finset (Fin n), T ∩ K = S₁ ∩ K → T ∈ 𝒜)
  (hKA₂ : ∀ T : Finset (Fin n), T ∩ K = S₂ ∩ K → T ∈ 𝒜)
  (hKcB₁ : ∀ T : Finset (Fin n), T ∩ Kᶜ = S₁ ∩ Kᶜ → T ∈ ℬ)
  (hKcB₂ : ∀ T : Finset (Fin n), T ∩ Kᶜ = S₂ ∩ Kᶜ → T ∈ ℬ)
  (htrace : S₁ ∩ K ≠ S₂ ∩ K) :
-- imply
  rc65_MarriageTwoPair 𝒜 ℬ S₁ S₂ := by
-- proof
  apply StatMech.Walls.rc65_marriage_two_of_commonWitness 𝒜 ℬ hKA₁ hKA₂ hKcB₁ hKcB₂ htrace

/--
[rc65_marriage_two_of_singletonInjective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc65marriagetwo.lean)
-/
@[path]
private lemma rc65_marriage_two_of_singletonInjective_eq
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {S₁ S₂ : Finset (Fin n)}
-- given
  (h : rc65_SingletonNbhdInjective)
  (hS₁ : S₁ ∈ rc20_famCylBox 𝒜 ℬ)
  (hS₂ : S₂ ∈ rc20_famCylBox 𝒜 ℬ)
  (hne : S₁ ≠ S₂) :
-- imply
  rc65_MarriageTwoPair 𝒜 ℬ S₁ S₂ := by
-- proof
  apply StatMech.Walls.rc65_marriage_two_of_singletonInjective h 𝒜 ℬ hS₁ hS₂ hne

/--
[rc65_singletonInjective_of_marriageTwo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc65marriagetwo.lean)
-/
@[path]
private lemma rc65_singletonInjective_of_marriageTwo_eq
  {n : ℕ}
-- given
  (h : ∀ (m : ℕ) (𝒜 ℬ : Finset (Finset (Fin m))) {S₁ S₂ : Finset (Fin m)}, S₁ ∈ rc20_famCylBox 𝒜 ℬ → S₂ ∈ rc20_famCylBox 𝒜 ℬ → S₁ ≠ S₂ → rc65_MarriageTwoPair 𝒜 ℬ S₁ S₂) :
-- imply
  rc65_SingletonNbhdInjective := by
-- proof
  apply StatMech.Walls.rc65_singletonInjective_of_marriageTwo h

/--
[rc65_marriageTwo_iff_singletonInjective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc65marriagetwo.lean)
-/
@[path]
private lemma rc65_marriageTwo_iff_singletonInjective_eq
  {n : ℕ} :
-- imply
  (∀ (m : ℕ) (𝒜 ℬ : Finset (Finset (Fin m))) {S₁ S₂ : Finset (Fin m)}, S₁ ∈ rc20_famCylBox 𝒜 ℬ → S₂ ∈ rc20_famCylBox 𝒜 ℬ → S₁ ≠ S₂ → rc65_MarriageTwoPair 𝒜 ℬ S₁ S₂) ↔ rc65_SingletonNbhdInjective := by
-- proof
  apply StatMech.Walls.rc65_marriageTwo_iff_singletonInjective

/--
[rc65_marriage_subfamily_two_of_singletonInjective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc65marriagetwo.lean)
-/
@[path]
private lemma rc65_marriage_subfamily_two_of_singletonInjective_eq
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {𝒯 : Finset (Finset (Fin n))}
-- given
  (h : rc65_SingletonNbhdInjective)
  (h𝒯 : 𝒯 ⊆ rc20_famCylBox 𝒜 ℬ)
  (hcard : 𝒯.card = 2) :
-- imply
  𝒯.card ≤ (𝒯.biUnion (rc59_nbhd 𝒜 ℬ)).card := by
-- proof
  apply StatMech.Walls.rc65_marriage_subfamily_two_of_singletonInjective h 𝒜 ℬ h𝒯 hcard

/--
[rc65_marriage_card_le_two_of_singletonInjective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc65marriagetwo.lean)
-/
@[path]
private lemma rc65_marriage_card_le_two_of_singletonInjective_eq
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {𝒯 : Finset (Finset (Fin n))}
-- given
  (h : rc65_SingletonNbhdInjective)
  (h𝒯 : 𝒯 ⊆ rc20_famCylBox 𝒜 ℬ)
  (hcard : 𝒯.card ≤ 2) :
-- imply
  𝒯.card ≤ (𝒯.biUnion (rc59_nbhd 𝒜 ℬ)).card := by
-- proof
  apply StatMech.Walls.rc65_marriage_card_le_two_of_singletonInjective h 𝒜 ℬ h𝒯 hcard

/--
[rc65_marriageTwoPair_fin2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc65marriagetwo.lean)
-/
@[path]
private lemma rc65_marriageTwoPair_fin2_eq
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin 2))}
  {S₁ S₂ : Finset (Fin 2)}
-- given
  (hS₁ : S₁ ∈ rc20_famCylBox 𝒜 ℬ)
  (hS₂ : S₂ ∈ rc20_famCylBox 𝒜 ℬ)
  (hne : S₁ ≠ S₂) :
-- imply
  rc65_MarriageTwoPair 𝒜 ℬ S₁ S₂ := by
-- proof
  apply StatMech.Walls.rc65_marriageTwoPair_fin2 𝒜 ℬ hS₁ hS₂ hne

/--
[rc65_singletonInjective_fin2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc65marriagetwo.lean)
-/
@[path]
private lemma rc65_singletonInjective_fin2_eq
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin 2))}
  {S₁ S₂ : Finset (Fin 2)}
  {R : Finset (Fin 2)}
-- given
  (hS₁ : S₁ ∈ rc20_famCylBox 𝒜 ℬ)
  (hS₂ : S₂ ∈ rc20_famCylBox 𝒜 ℬ)
  (hne : S₁ ≠ S₂)
  (hR₁ : rc59_nbhd 𝒜 ℬ S₁ = {R})
  (hR₂ : rc59_nbhd 𝒜 ℬ S₂ = {R}) :
-- imply
  False := by
-- proof
  apply StatMech.Walls.rc65_singletonInjective_fin2 𝒜 ℬ hS₁ hS₂ hne R hR₁ hR₂

/--
[rc65_marriageTwoPair_fin3_refuter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc65marriagetwo.lean)
-/
@[path]
private lemma rc65_marriageTwoPair_fin3_refuter_eq
  {n : ℕ}
  {S₁ S₂ : Finset (Fin 3)}
-- given
  (hS₁ : S₁ ∈ rc20_famCylBox rc32_A3 rc32_B3)
  (hS₂ : S₂ ∈ rc20_famCylBox rc32_A3 rc32_B3)
  (hne : S₁ ≠ S₂) :
-- imply
  rc65_MarriageTwoPair rc32_A3 rc32_B3 S₁ S₂ := by
-- proof
  apply StatMech.Walls.rc65_marriageTwoPair_fin3_refuter hS₁ hS₂ hne

/--
[rc65_refuter_box_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc65marriagetwo.lean)
-/
@[path]
private lemma rc65_refuter_box_two_eq
  {n : ℕ} :
-- imply
  rc21_boxComp 3 rc40_Aref rc40_Bref = {{0}, {1}} := by
-- proof
  apply StatMech.Walls.rc65_refuter_box_two

/--
[rc65_refuter_R0values_collapse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc65marriagetwo.lean)
-/
@[path]
private lemma rc65_refuter_R0values_collapse_eq
  {n : ℕ} :
-- imply
  rc40_R0valuesComp 3 rc40_Aref rc40_Bref {0} = {∅} ∧ rc40_R0valuesComp 3 rc40_Aref rc40_Bref {1} = {∅} := by
-- proof
  apply StatMech.Walls.rc65_refuter_R0values_collapse

/--
[rc65_refuter_R0_insufficient_for_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc65marriagetwo.lean)
-/
@[path]
private lemma rc65_refuter_R0_insufficient_for_two_eq
  {n : ℕ} :
-- imply
  (({{0}, {1}} : Finset (Finset (Fin 3))).biUnion (rc40_R0valuesComp 3 rc40_Aref rc40_Bref)).card < (rc21_boxComp 3 rc40_Aref rc40_Bref).card := by
-- proof
  apply StatMech.Walls.rc65_refuter_R0_insufficient_for_two

/--
[rc65_refuter_hall_holds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc65marriagetwo.lean)
-/
@[path]
private lemma rc65_refuter_hall_holds_eq
  {n : ℕ} :
-- imply
  rc33_hallOneSidedA 3 rc40_Aref rc40_Bref = true := by
-- proof
  apply StatMech.Walls.rc65_refuter_hall_holds

/--
[rc65_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc65marriagetwo.lean)
-/
@[path]
private lemma rc65_status_eq
  {n : ℕ} :
-- imply
  ((∀ (m : ℕ) (𝒜 ℬ : Finset (Finset (Fin m))) {S₁ S₂ : Finset (Fin m)}, S₁ ∈ rc20_famCylBox 𝒜 ℬ → S₂ ∈ rc20_famCylBox 𝒜 ℬ → S₁ ≠ S₂ → rc65_MarriageTwoPair 𝒜 ℬ S₁ S₂) ↔ rc65_SingletonNbhdInjective) ∧ (rc65_SingletonNbhdInjective → ∀ (m : ℕ) (𝒜 ℬ : Finset (Finset (Fin m))) (𝒯 : Finset (Finset (Fin m))), 𝒯 ⊆ rc20_famCylBox 𝒜 ℬ → 𝒯.card ≤ 2 → 𝒯.card ≤ (𝒯.biUnion (rc59_nbhd 𝒜 ℬ)).card) ∧ (∀ (m : ℕ) (𝒜 ℬ : Finset (Finset (Fin m))) {S₁ S₂ K : Finset (Fin m)}, (∀ T : Finset (Fin m), T ∩ K = S₁ ∩ K → T ∈ 𝒜) → (∀ T : Finset (Fin m), T ∩ K = S₂ ∩ K → T ∈ 𝒜) → (∀ T : Finset (Fin m), T ∩ Kᶜ = S₁ ∩ Kᶜ → T ∈ ℬ) → (∀ T : Finset (Fin m), T ∩ Kᶜ = S₂ ∩ Kᶜ → T ∈ ℬ) → S₁ ∩ K ≠ S₂ ∩ K → rc65_MarriageTwoPair 𝒜 ℬ S₁ S₂) ∧ (∀ (𝒜 ℬ : Finset (Finset (Fin 2))) {S₁ S₂ : Finset (Fin 2)}, S₁ ∈ rc20_famCylBox 𝒜 ℬ → S₂ ∈ rc20_famCylBox 𝒜 ℬ → S₁ ≠ S₂ → ∀ R : Finset (Fin 2), rc59_nbhd 𝒜 ℬ S₁ = {R} → rc59_nbhd 𝒜 ℬ S₂ = {R} → False) ∧ (∀ {S₁ S₂ : Finset (Fin 3)}, S₁ ∈ rc20_famCylBox rc32_A3 rc32_B3 → S₂ ∈ rc20_famCylBox rc32_A3 rc32_B3 → S₁ ≠ S₂ → rc65_MarriageTwoPair rc32_A3 rc32_B3 S₁ S₂) ∧ (rc21_boxComp 3 rc40_Aref rc40_Bref = {{0}, {1}}) ∧ ((({{0}, {1}} : Finset (Finset (Fin 3))).biUnion (rc40_R0valuesComp 3 rc40_Aref rc40_Bref)).card < (rc21_boxComp 3 rc40_Aref rc40_Bref).card) ∧ (rc33_hallOneSidedA 3 rc40_Aref rc40_Bref = true) := by
-- proof
  apply StatMech.Walls.rc65_status


-- created on 2026-10-23
