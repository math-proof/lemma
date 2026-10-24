import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.rc48cover
open Finset StatMech StatMech.Walls


/--
[rc48_compl_mem_reflInter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc48cover.lean)
-/
@[path]
private lemma rc48_compl_mem_reflInter_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {S : Finset α}
-- given
  (hS : S ∈ rc20_famCylBox 𝒜 ℬ)
  (hSc : Sᶜ ∈ 𝒜) :
-- imply
  Sᶜ ∈ rc10_reflInter 𝒜 ℬ := by
-- proof
  apply StatMech.Walls.rc48_compl_mem_reflInter hS hSc

/--
[rc48_famCylBox_le_reflInter_of_complSubset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc48cover.lean)
-/
@[path]
private lemma rc48_famCylBox_le_reflInter_of_complSubset_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
-- given
  (h : ∀ S ∈ rc20_famCylBox 𝒜 ℬ, Sᶜ ∈ 𝒜) :
-- imply
  #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) := by
-- proof
  apply StatMech.Walls.rc48_famCylBox_le_reflInter_of_complSubset 𝒜 ℬ h

/--
[rc48_reflInter_mono_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc48cover.lean)
-/
@[path]
private lemma rc48_reflInter_mono_left_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 𝒜' ℬ : Finset (Finset α)}
-- given
  (h : 𝒜 ⊆ 𝒜') :
-- imply
  rc10_reflInter 𝒜 ℬ ⊆ rc10_reflInter 𝒜' ℬ := by
-- proof
  apply StatMech.Walls.rc48_reflInter_mono_left h

/--
[rc48_reflInter_mono_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc48cover.lean)
-/
@[path]
private lemma rc48_reflInter_mono_right_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ ℬ' : Finset (Finset α)}
-- given
  (h : ℬ ⊆ ℬ') :
-- imply
  rc10_reflInter 𝒜 ℬ ⊆ rc10_reflInter 𝒜 ℬ' := by
-- proof
  apply StatMech.Walls.rc48_reflInter_mono_right h

/--
[rc48_wall_of_cover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc48cover.lean)
-/
@[path]
private lemma rc48_wall_of_cover_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
-- given
  (h : #(𝒜 ∩ ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) ∨ rc20_famCylBox 𝒜 ℬ ⊆ rc10_reflInter 𝒜 ℬ ∨ (∀ S ∈ rc20_famCylBox 𝒜 ℬ, Sᶜ ∈ 𝒜)) :
-- imply
  #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) := by
-- proof
  apply StatMech.Walls.rc48_wall_of_cover 𝒜 ℬ h

/--
[rc48_reimer_closes_of_coverAll](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc48cover.lean)
-/
@[path]
private lemma rc48_reimer_closes_of_coverAll_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : rc48_CoverAll) :
-- imply
  rc18_CylBoxReflInter := by
-- proof
  apply StatMech.Walls.rc48_reimer_closes_of_coverAll h

/--
[rc48_complSubset_fires_fin3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc48cover.lean)
-/
@[path]
private lemma rc48_complSubset_fires_fin3_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  ∀ S ∈ rc20_famCylBoxComp 3 rc48_C₁ rc48_D₁, Sᶜ ∈ rc48_C₁ := by
-- proof
  apply StatMech.Walls.rc48_complSubset_fires_fin3

/--
[rc48_boxSubReflInter_fails_C](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc48cover.lean)
-/
@[path]
private lemma rc48_boxSubReflInter_fails_C_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  ¬ (rc20_famCylBoxComp 3 rc48_C₁ rc48_D₁ ⊆ rc20_reflInterComp 3 rc48_C₁ rc48_D₁) := by
-- proof
  apply StatMech.Walls.rc48_boxSubReflInter_fails_C

/--
[rc48_interCard_fails_C](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc48cover.lean)
-/
@[path]
private lemma rc48_interCard_fails_C_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (rc20_reflInterComp 3 rc48_C₁ rc48_D₁).card < #(rc48_C₁ ∩ rc48_D₁) := by
-- proof
  apply StatMech.Walls.rc48_interCard_fails_C

/--
[rc48_wall_C](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc48cover.lean)
-/
@[path]
private lemma rc48_wall_C_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  #(rc20_famCylBox rc48_C₁ rc48_D₁) ≤ #(rc10_reflInter rc48_C₁ rc48_D₁) := by
-- proof
  apply StatMech.Walls.rc48_wall_C

/--
[rc48_residual_c1_fails_fin3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc48cover.lean)
-/
@[path]
private lemma rc48_residual_c1_fails_fin3_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (rc20_reflInterComp 3 rc48_A₂ rc48_B₂).card < #(rc48_A₂ ∩ rc48_B₂) := by
-- proof
  apply StatMech.Walls.rc48_residual_c1_fails_fin3

/--
[rc48_residual_c2_fails_fin3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc48cover.lean)
-/
@[path]
private lemma rc48_residual_c2_fails_fin3_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  ¬ (rc20_famCylBoxComp 3 rc48_A₂ rc48_B₂ ⊆ rc20_reflInterComp 3 rc48_A₂ rc48_B₂) := by
-- proof
  apply StatMech.Walls.rc48_residual_c2_fails_fin3

/--
[rc48_residual_c3_fails_fin3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc48cover.lean)
-/
@[path]
private lemma rc48_residual_c3_fails_fin3_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  ¬ (∀ S ∈ rc20_famCylBoxComp 3 rc48_A₂ rc48_B₂, Sᶜ ∈ rc48_A₂) := by
-- proof
  apply StatMech.Walls.rc48_residual_c3_fails_fin3

/--
[rc48_wall_A](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc48cover.lean)
-/
@[path]
private lemma rc48_wall_A_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (rc20_famCylBoxComp 3 rc48_A₂ rc48_B₂).card ≤ (rc20_reflInterComp 3 rc48_A₂ rc48_B₂).card := by
-- proof
  apply StatMech.Walls.rc48_wall_A

/--
[rc48_famCylBox_not_compressionInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc48cover.lean)
-/
@[path]
private lemma rc48_famCylBox_not_compressionInvariant_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (rc20_famCylBoxComp 3 (rc48_downCompress 3 0 rc48_A₂) (rc48_downCompress 3 0 rc48_E₂)).card ≠ (rc20_famCylBoxComp 3 rc48_A₂ rc48_E₂).card := by
-- proof
  apply StatMech.Walls.rc48_famCylBox_not_compressionInvariant

/--
[rc48_reimer_threeway_cover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc48cover.lean)
-/
@[path]
private lemma rc48_reimer_threeway_cover_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (∀ (𝒜 ℬ : Finset (Finset (Fin 3))), (∀ S ∈ rc20_famCylBox 𝒜 ℬ, Sᶜ ∈ 𝒜) → #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ)) ∧ (∀ (𝒜 ℬ : Finset (Finset (Fin 3))), #(𝒜 ∩ ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) ∨ rc20_famCylBox 𝒜 ℬ ⊆ rc10_reflInter 𝒜 ℬ ∨ (∀ S ∈ rc20_famCylBox 𝒜 ℬ, Sᶜ ∈ 𝒜) → #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ)) ∧ (rc48_CoverAll → rc18_CylBoxReflInter) ∧ (#(rc20_famCylBox rc48_C₁ rc48_D₁) ≤ #(rc10_reflInter rc48_C₁ rc48_D₁)) ∧ (¬ (rc20_famCylBoxComp 3 rc48_C₁ rc48_D₁ ⊆ rc20_reflInterComp 3 rc48_C₁ rc48_D₁)) ∧ ((rc20_reflInterComp 3 rc48_A₂ rc48_B₂).card < #(rc48_A₂ ∩ rc48_B₂)) ∧ ((rc20_famCylBoxComp 3 rc48_A₂ rc48_B₂).card ≤ (rc20_reflInterComp 3 rc48_A₂ rc48_B₂).card) ∧ ((rc20_famCylBoxComp 3 (rc48_downCompress 3 0 rc48_A₂) (rc48_downCompress 3 0 rc48_E₂)).card ≠ (rc20_famCylBoxComp 3 rc48_A₂ rc48_E₂).card) := by
-- proof
  apply StatMech.Walls.rc48_reimer_threeway_cover


-- created on 2026-10-23
