import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.rc20reflection
open Finset StatMech StatMech.Walls


/--
[rc20_mem_eventFamily_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc20reflection.lean)
-/
@[path]
private lemma rc20_mem_eventFamily_iff_eq
  [Fintype α]
  [DecidableEq α]
  {A : Set (ConfigSpace α)}
  {S : Finset α} :
-- imply
  S ∈ eventFamily A ↔ supportCfg S ∈ A := by
-- proof
  apply StatMech.Walls.rc20_mem_eventFamily_iff A S

/--
[rc20_eventFamily_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc20reflection.lean)
-/
@[path]
private lemma rc20_eventFamily_univ_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  eventFamily (Set.univ : Set (ConfigSpace α)) = univ := by
-- proof
  apply StatMech.Walls.rc20_eventFamily_univ

/--
[rc20_agree_iff_inter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc20reflection.lean)
-/
@[path]
private lemma rc20_agree_iff_inter_eq
  [Fintype α]
  [DecidableEq α]
  {K S T : Finset α} :
-- imply
  (∀ e ∈ K, supportCfg T e = supportCfg S e) ↔ T ∩ K = S ∩ K := by
-- proof
  apply StatMech.Walls.rc20_agree_iff_inter K S T

/--
[rc20_cylinder_subset_iff_family](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc20reflection.lean)
-/
@[path]
private lemma rc20_cylinder_subset_iff_family_eq
  [Fintype α]
  [DecidableEq α]
  {A : Set (ConfigSpace α)}
  {K S : Finset α} :
-- imply
  cylinder K (supportCfg S) ⊆ A ↔ ∀ T : Finset α, T ∩ K = S ∩ K → T ∈ eventFamily A := by
-- proof
  apply StatMech.Walls.rc20_cylinder_subset_iff_family A K S

/--
[rc20_cylBoxSupp_self_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc20reflection.lean)
-/
@[path]
private lemma rc20_cylBoxSupp_self_mem_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
  {S : Finset α}
-- given
  (hS : S ∈ rc18_cylBoxSupp A B) :
-- imply
  supportCfg S ∈ A ∧ supportCfg S ∈ B := by
-- proof
  apply StatMech.Walls.rc20_cylBoxSupp_self_mem hS

/--
[rc20_cylBoxSupp_mem_eventFamily](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc20reflection.lean)
-/
@[path]
private lemma rc20_cylBoxSupp_mem_eventFamily_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
  {S : Finset α}
-- given
  (hS : S ∈ rc18_cylBoxSupp A B) :
-- imply
  S ∈ eventFamily A := by
-- proof
  apply StatMech.Walls.rc20_cylBoxSupp_mem_eventFamily hS

/--
[rc20_cylBoxSupp_eq_famCylBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc20reflection.lean)
-/
@[path]
private lemma rc20_cylBoxSupp_eq_famCylBox_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)} :
-- imply
  rc18_cylBoxSupp A B = rc20_famCylBox (eventFamily A) (eventFamily B) := by
-- proof
  apply StatMech.Walls.rc20_cylBoxSupp_eq_famCylBox A B

/--
[rc20_mem_reflInter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc20reflection.lean)
-/
@[path]
private lemma rc20_mem_reflInter_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {S : Finset α} :
-- imply
  S ∈ rc10_reflInter 𝒜 ℬ ↔ S ∈ 𝒜 ∧ Sᶜ ∈ ℬ := by
-- proof
  apply StatMech.Walls.rc20_mem_reflInter 𝒜 ℬ S

/--
[rc20_cylBoxReflInter_of_famCylBoxResidue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc20reflection.lean)
-/
@[path]
private lemma rc20_cylBoxReflInter_of_famCylBoxResidue_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : rc20_FamCylBoxResidue) :
-- imply
  rc18_CylBoxReflInter := by
-- proof
  apply StatMech.Walls.rc20_cylBoxReflInter_of_famCylBoxResidue h

/--
[rc20_famCylBoxResidue_of_cylBoxReflInter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc20reflection.lean)
-/
@[path]
private lemma rc20_famCylBoxResidue_of_cylBoxReflInter_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : rc18_CylBoxReflInter) :
-- imply
  rc20_FamCylBoxResidue := by
-- proof
  apply StatMech.Walls.rc20_famCylBoxResidue_of_cylBoxReflInter h

/--
[rc20_famCylBoxResidue_iff_cylBoxReflInter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc20reflection.lean)
-/
@[path]
private lemma rc20_famCylBoxResidue_iff_cylBoxReflInter_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc20_FamCylBoxResidue ↔ rc18_CylBoxReflInter := by
-- proof
  apply StatMech.Walls.rc20_famCylBoxResidue_iff_cylBoxReflInter

/--
[rc20_doubledReflection_right_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc20reflection.lean)
-/
@[path]
private lemma rc20_doubledReflection_right_univ_eq
  [Fintype α]
  [DecidableEq α]
  {A : Set (ConfigSpace α)} :
-- imply
  rc19_DoubledReflection A (Set.univ : Set (ConfigSpace α)) := by
-- proof
  apply StatMech.Walls.rc20_doubledReflection_right_univ A

/--
[rc20_doubledReflection_left_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc20reflection.lean)
-/
@[path]
private lemma rc20_doubledReflection_left_univ_eq
  [Fintype α]
  [DecidableEq α]
  {B : Set (ConfigSpace α)} :
-- imply
  rc19_DoubledReflection (Set.univ : Set (ConfigSpace α)) B := by
-- proof
  apply StatMech.Walls.rc20_doubledReflection_left_univ B

/--
[rc20_traceClass_subset_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc20reflection.lean)
-/
@[path]
private lemma rc20_traceClass_subset_iff_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {K S : Finset (Fin n)}
  {𝒜 : Finset (Finset (Fin n))} :
-- imply
  rc20_traceClass n K S ⊆ 𝒜 ↔ ∀ T : Finset (Fin n), T ∩ K = S ∩ K → T ∈ 𝒜 := by
-- proof
  apply StatMech.Walls.rc20_traceClass_subset_iff n K S 𝒜

/--
[rc20_famCylBoxComp_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc20reflection.lean)
-/
@[path]
private lemma rc20_famCylBoxComp_eq_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))} :
-- imply
  rc20_famCylBoxComp n 𝒜 ℬ = rc20_famCylBox 𝒜 ℬ := by
-- proof
  apply StatMech.Walls.rc20_famCylBoxComp_eq n 𝒜 ℬ

/--
[rc20_reflInterComp_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc20reflection.lean)
-/
@[path]
private lemma rc20_reflInterComp_eq_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))} :
-- imply
  rc20_reflInterComp n 𝒜 ℬ = rc10_reflInter 𝒜 ℬ := by
-- proof
  apply StatMech.Walls.rc20_reflInterComp_eq n 𝒜 ℬ

/--
[rc20_famCylBox_card_le_iff_comp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc20reflection.lean)
-/
@[path]
private lemma rc20_famCylBox_card_le_iff_comp_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))} :
-- imply
  #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) ↔ (rc20_famCylBoxComp n 𝒜 ℬ).card ≤ (rc20_reflInterComp n 𝒜 ℬ).card := by
-- proof
  apply StatMech.Walls.rc20_famCylBox_card_le_iff_comp n 𝒜 ℬ

/--
[rc20_famCylBox_fin0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc20reflection.lean)
-/
@[path]
private lemma rc20_famCylBox_fin0_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset (Fin 0))} :
-- imply
  #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) := by
-- proof
  apply StatMech.Walls.rc20_famCylBox_fin0 𝒜 ℬ

/--
[rc20_famCylBox_fin1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc20reflection.lean)
-/
@[path]
private lemma rc20_famCylBox_fin1_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset (Fin 1))} :
-- imply
  #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) := by
-- proof
  apply StatMech.Walls.rc20_famCylBox_fin1 𝒜 ℬ

/--
[rc20_famCylBox_fin2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc20reflection.lean)
-/
@[path]
private lemma rc20_famCylBox_fin2_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset (Fin 2))} :
-- imply
  #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) := by
-- proof
  apply StatMech.Walls.rc20_famCylBox_fin2 𝒜 ℬ

/--
[rc20_cylBoxReflInter_fin2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc20reflection.lean)
-/
@[path]
private lemma rc20_cylBoxReflInter_fin2_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace (Fin 2))} :
-- imply
  #(rc18_cylBoxSupp A B) ≤ #(rc10_reflInter (eventFamily A) (eventFamily B)) := by
-- proof
  apply StatMech.Walls.rc20_cylBoxReflInter_fin2 A B

/--
[rc20_doubledReflection_fin2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc20reflection.lean)
-/
@[path]
private lemma rc20_doubledReflection_fin2_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace (Fin 2))} :
-- imply
  rc19_DoubledReflection A B := by
-- proof
  apply StatMech.Walls.rc20_doubledReflection_fin2 A B

/--
[rc20_doubledReflection_fin1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc20reflection.lean)
-/
@[path]
private lemma rc20_doubledReflection_fin1_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace (Fin 1))} :
-- imply
  rc19_DoubledReflection A B := by
-- proof
  apply StatMech.Walls.rc20_doubledReflection_fin1 A B

/--
[rc20_doubledReflection_fin0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc20reflection.lean)
-/
@[path]
private lemma rc20_doubledReflection_fin0_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace (Fin 0))} :
-- imply
  rc19_DoubledReflection A B := by
-- proof
  apply StatMech.Walls.rc20_doubledReflection_fin0 A B

/--
[rc20_identityMirror_insufficient](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc20reflection.lean)
-/
@[path]
private lemma rc20_identityMirror_insufficient_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  ∃ (𝒜 ℬ : Finset (Finset (Fin 2))) (S : Finset (Fin 2)), S ∈ rc20_famCylBox 𝒜 ℬ ∧ S ∉ rc10_reflInter 𝒜 ℬ := by
-- proof
  apply StatMech.Walls.rc20_identityMirror_insufficient

/--
[rc20_famCylBox_mono_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc20reflection.lean)
-/
@[path]
private lemma rc20_famCylBox_mono_left_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 𝒜' ℬ : Finset (Finset α)}
-- given
  (h : 𝒜 ⊆ 𝒜') :
-- imply
  rc20_famCylBox 𝒜 ℬ ⊆ rc20_famCylBox 𝒜' ℬ := by
-- proof
  apply StatMech.Walls.rc20_famCylBox_mono_left h

/--
[rc20_famCylBox_mono_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc20reflection.lean)
-/
@[path]
private lemma rc20_famCylBox_mono_right_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ ℬ' : Finset (Finset α)}
-- given
  (h : ℬ ⊆ ℬ') :
-- imply
  rc20_famCylBox 𝒜 ℬ ⊆ rc20_famCylBox 𝒜 ℬ' := by
-- proof
  apply StatMech.Walls.rc20_famCylBox_mono_right h

/--
[rc20_famCylBox_of_increasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc20reflection.lean)
-/
@[path]
private lemma rc20_famCylBox_of_increasing_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {A B : Set (ConfigSpace (Fin n))}
-- given
  (hA : IsIncreasing A)
  (hB : IsIncreasing B) :
-- imply
  #(rc20_famCylBox (eventFamily A) (eventFamily B)) ≤ #(rc10_reflInter (eventFamily A) (eventFamily B)) := by
-- proof
  apply StatMech.Walls.rc20_famCylBox_of_increasing hA hB

/--
[rc20_doubledReflection_rbi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc20reflection.lean)
-/
@[path]
private lemma rc20_doubledReflection_rbi_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  ((¬ IsIncreasing rbi_B ∧ ¬ IsDecreasing rbi_B)) ∧ rc19_DoubledReflection rbi_A rbi_B := by
-- proof
  apply StatMech.Walls.rc20_doubledReflection_rbi

/--
[rc20_perSupportReflection_iff_famCylBoxResidue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc20reflection.lean)
-/
@[path]
private lemma rc20_perSupportReflection_iff_famCylBoxResidue_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc20_PerSupportReflection ↔ rc20_FamCylBoxResidue := by
-- proof
  apply StatMech.Walls.rc20_perSupportReflection_iff_famCylBoxResidue

/--
[rc20_perSupportReflection_iff_cylBoxReflInter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc20reflection.lean)
-/
@[path]
private lemma rc20_perSupportReflection_iff_cylBoxReflInter_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc20_PerSupportReflection ↔ rc18_CylBoxReflInter := by
-- proof
  apply StatMech.Walls.rc20_perSupportReflection_iff_cylBoxReflInter

/--
[rc20_perSupportReflection_satisfiable_rbi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc20reflection.lean)
-/
@[path]
private lemma rc20_perSupportReflection_satisfiable_rbi_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  ∃ f : Finset (Fin 2) → Finset (Fin 2), Set.InjOn f (rc20_famCylBox ({∅, {0}, {1}} : Finset (Finset (Fin 2))) ({∅, {1}, {0, 1}}) : Set (Finset (Fin 2))) ∧ ∀ S ∈ rc20_famCylBox ({∅, {0}, {1}} : Finset (Finset (Fin 2))) ({∅, {1}, {0, 1}}), f S ∈ rc10_reflInter ({∅, {0}, {1}} : Finset (Finset (Fin 2))) ({∅, {1}, {0, 1}}) := by
-- proof
  apply StatMech.Walls.rc20_perSupportReflection_satisfiable_rbi

/--
[rc20_reimer_reflection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc20reflection.lean)
-/
@[path]
private lemma rc20_reimer_reflection_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (rc20_FamCylBoxResidue ↔ rc18_CylBoxReflInter) ∧ (rc20_PerSupportReflection ↔ rc18_CylBoxReflInter) ∧ (∀ A B : Set (ConfigSpace (Fin 2)), rc19_DoubledReflection A B) ∧ (∀ A : Set (ConfigSpace α), rc19_DoubledReflection A (Set.univ : Set (ConfigSpace α))) ∧ (∀ B : Set (ConfigSpace α), rc19_DoubledReflection (Set.univ : Set (ConfigSpace α)) B) ∧ (∃ (𝒜 ℬ : Finset (Finset (Fin 2))) (S : Finset (Fin 2)), S ∈ rc20_famCylBox 𝒜 ℬ ∧ S ∉ rc10_reflInter 𝒜 ℬ) := by
-- proof
  apply StatMech.Walls.rc20_reimer_reflection


-- created on 2026-10-23
