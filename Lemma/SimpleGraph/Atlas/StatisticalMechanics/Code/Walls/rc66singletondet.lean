import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.rc66singletondet
open Finset StatMech StatMech.Walls


/--
[rc66_mem_nbhd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc66singletondet.lean)
-/
@[path]
private lemma rc66_mem_nbhd_eq
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {S R : Finset (Fin n)} :
-- imply
  R ∈ rc59_nbhd 𝒜 ℬ S ↔ R ∈ 𝒜 ∧ Rᶜ ∈ ℬ ∧ ∃ K : Finset (Fin n), (∀ T : Finset (Fin n), T ∩ K = S ∩ K → T ∈ 𝒜) ∧ R ∩ K = S ∩ K := by
-- proof
  apply StatMech.Walls.rc66_mem_nbhd 𝒜 ℬ S R

/--
[rc66_self_mem_nbhd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc66singletondet.lean)
-/
@[path]
private lemma rc66_self_mem_nbhd_eq
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {S : Finset (Fin n)}
-- given
  (hbox : S ∈ rc20_famCylBox 𝒜 ℬ)
  (hRI : S ∈ rc10_reflInter 𝒜 ℬ) :
-- imply
  S ∈ rc59_nbhd 𝒜 ℬ S := by
-- proof
  apply StatMech.Walls.rc66_self_mem_nbhd 𝒜 ℬ hbox hRI

/--
[rc66_singleton_nbhd_forces_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc66singletondet.lean)
-/
@[path]
private lemma rc66_singleton_nbhd_forces_self_eq
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {S R : Finset (Fin n)}
-- given
  (hbox : S ∈ rc20_famCylBox 𝒜 ℬ)
  (hRI : S ∈ rc10_reflInter 𝒜 ℬ)
  (hnb : rc59_nbhd 𝒜 ℬ S = {R}) :
-- imply
  R = S := by
-- proof
  apply StatMech.Walls.rc66_singleton_nbhd_forces_self 𝒜 ℬ hbox hRI hnb

/--
[rc66_singletonInjective_on_reflInter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc66singletondet.lean)
-/
@[path]
private lemma rc66_singletonInjective_on_reflInter_eq
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {S₁ S₂ : Finset (Fin n)}
  {R : Finset (Fin n)}
-- given
  (hbox₁ : S₁ ∈ rc20_famCylBox 𝒜 ℬ)
  (hRI₁ : S₁ ∈ rc10_reflInter 𝒜 ℬ)
  (hbox₂ : S₂ ∈ rc20_famCylBox 𝒜 ℬ)
  (hRI₂ : S₂ ∈ rc10_reflInter 𝒜 ℬ)
  (hne : S₁ ≠ S₂)
  (hR₁ : rc59_nbhd 𝒜 ℬ S₁ = {R})
  (hR₂ : rc59_nbhd 𝒜 ℬ S₂ = {R}) :
-- imply
  False := by
-- proof
  apply StatMech.Walls.rc66_singletonInjective_on_reflInter 𝒜 ℬ hbox₁ hRI₁ hbox₂ hRI₂ hne R hR₁ hR₂

/--
[rc66_marriageTwoPair_on_reflInter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc66singletondet.lean)
-/
@[path]
private lemma rc66_marriageTwoPair_on_reflInter_eq
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {S₁ S₂ : Finset (Fin n)}
-- given
  (hbox₁ : S₁ ∈ rc20_famCylBox 𝒜 ℬ)
  (hRI₁ : S₁ ∈ rc10_reflInter 𝒜 ℬ)
  (hbox₂ : S₂ ∈ rc20_famCylBox 𝒜 ℬ)
  (hRI₂ : S₂ ∈ rc10_reflInter 𝒜 ℬ)
  (hne : S₁ ≠ S₂) :
-- imply
  rc65_MarriageTwoPair 𝒜 ℬ S₁ S₂ := by
-- proof
  apply StatMech.Walls.rc66_marriageTwoPair_on_reflInter 𝒜 ℬ hbox₁ hRI₁ hbox₂ hRI₂ hne

/--
[rc66_singletonInjective_fin2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc66singletondet.lean)
-/
@[path]
private lemma rc66_singletonInjective_fin2_eq
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
  apply StatMech.Walls.rc66_singletonInjective_fin2 𝒜 ℬ hS₁ hS₂ hne R hR₁ hR₂

/--
[rc66_witness_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc66singletondet.lean)
-/
@[path]
private lemma rc66_witness_box_eq
  {n : ℕ} :
-- imply
  ({0} : Finset (Fin 2)) ∈ rc20_famCylBox rc66_wA rc66_wB ∧ (∅ : Finset (Fin 2)) ∈ rc20_famCylBox rc66_wA rc66_wB ∧ ({0} : Finset (Fin 2)) ≠ (∅ : Finset (Fin 2)) := by
-- proof
  apply StatMech.Walls.rc66_witness_box

/--
[rc66_witness_offReflInter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc66singletondet.lean)
-/
@[path]
private lemma rc66_witness_offReflInter_eq
  {n : ℕ} :
-- imply
  ({0} : Finset (Fin 2)) ∉ rc10_reflInter rc66_wA rc66_wB := by
-- proof
  apply StatMech.Walls.rc66_witness_offReflInter

/--
[rc66_witness_sharedNeighbour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc66singletondet.lean)
-/
@[path]
private lemma rc66_witness_sharedNeighbour_eq
  {n : ℕ} :
-- imply
  (∅ : Finset (Fin 2)) ∈ rc59_nbhd rc66_wA rc66_wB {0} ∧ (∅ : Finset (Fin 2)) ∈ rc59_nbhd rc66_wA rc66_wB (∅ : Finset (Fin 2)) := by
-- proof
  apply StatMech.Walls.rc66_witness_sharedNeighbour

/--
[rc66_witness_singleton_broken](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc66singletondet.lean)
-/
@[path]
private lemma rc66_witness_singleton_broken_eq
  {n : ℕ} :
-- imply
  rc59_nbhd rc66_wA rc66_wB {0} = {∅} ∧ rc59_nbhd rc66_wA rc66_wB (∅ : Finset (Fin 2)) ≠ {∅} := by
-- proof
  apply StatMech.Walls.rc66_witness_singleton_broken

/--
[rc66_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc66singletondet.lean)
-/
@[path]
private lemma rc66_status_eq
  {n : ℕ} :
-- imply
  (∀ (m : ℕ) (𝒜 ℬ : Finset (Finset (Fin m))) {S R : Finset (Fin m)}, S ∈ rc20_famCylBox 𝒜 ℬ → S ∈ rc10_reflInter 𝒜 ℬ → rc59_nbhd 𝒜 ℬ S = {R} → R = S) ∧ (∀ (m : ℕ) (𝒜 ℬ : Finset (Finset (Fin m))) {S₁ S₂ : Finset (Fin m)}, S₁ ∈ rc20_famCylBox 𝒜 ℬ → S₁ ∈ rc10_reflInter 𝒜 ℬ → S₂ ∈ rc20_famCylBox 𝒜 ℬ → S₂ ∈ rc10_reflInter 𝒜 ℬ → S₁ ≠ S₂ → ∀ R : Finset (Fin m), rc59_nbhd 𝒜 ℬ S₁ = {R} → rc59_nbhd 𝒜 ℬ S₂ = {R} → False) ∧ (∀ (𝒜 ℬ : Finset (Finset (Fin 2))) {S₁ S₂ : Finset (Fin 2)}, S₁ ∈ rc20_famCylBox 𝒜 ℬ → S₂ ∈ rc20_famCylBox 𝒜 ℬ → S₁ ≠ S₂ → ∀ R : Finset (Fin 2), rc59_nbhd 𝒜 ℬ S₁ = {R} → rc59_nbhd 𝒜 ℬ S₂ = {R} → False) ∧ (({0} : Finset (Fin 2)) ∈ rc20_famCylBox rc66_wA rc66_wB ∧ (∅ : Finset (Fin 2)) ∈ rc20_famCylBox rc66_wA rc66_wB ∧ ({0} : Finset (Fin 2)) ≠ (∅ : Finset (Fin 2))) ∧ ((∅ : Finset (Fin 2)) ∈ rc59_nbhd rc66_wA rc66_wB {0} ∧ (∅ : Finset (Fin 2)) ∈ rc59_nbhd rc66_wA rc66_wB (∅ : Finset (Fin 2))) ∧ (rc59_nbhd rc66_wA rc66_wB {0} = {∅} ∧ rc59_nbhd rc66_wA rc66_wB (∅ : Finset (Fin 2)) ≠ {∅}) := by
-- proof
  apply StatMech.Walls.rc66_status


-- created on 2026-10-23
