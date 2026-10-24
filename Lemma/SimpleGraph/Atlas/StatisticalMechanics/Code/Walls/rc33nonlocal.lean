import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.rc33nonlocal
open Finset StatMech StatMech.Walls


/--
[rc33_admOneSidedA_subset_reflInter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc33nonlocal.lean)
-/
@[path]
private lemma rc33_admOneSidedA_subset_reflInter_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {S : Finset (Fin n)} :
-- imply
  rc33_admOneSidedA n 𝒜 ℬ S ⊆ rc10_reflInter 𝒜 ℬ := by
-- proof
  apply StatMech.Walls.rc33_admOneSidedA_subset_reflInter n 𝒜 ℬ S

/--
[rc33_admOneSidedB_subset_reflInter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc33nonlocal.lean)
-/
@[path]
private lemma rc33_admOneSidedB_subset_reflInter_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {S : Finset (Fin n)} :
-- imply
  rc33_admOneSidedB n 𝒜 ℬ S ⊆ rc10_reflInter 𝒜 ℬ := by
-- proof
  apply StatMech.Walls.rc33_admOneSidedB_subset_reflInter n 𝒜 ℬ S

/--
[rc33_admComp_subset_bothSided](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc33nonlocal.lean)
-/
@[path]
private lemma rc33_admComp_subset_bothSided_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {S : Finset (Fin n)} :
-- imply
  rc21_admComp n 𝒜 ℬ S ⊆ rc33_admBothSided n 𝒜 ℬ S := by
-- proof
  apply StatMech.Walls.rc33_admComp_subset_bothSided n 𝒜 ℬ S

/--
[rc33_wall_of_hallOneSidedA](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc33nonlocal.lean)
-/
@[path]
private lemma rc33_wall_of_hallOneSidedA_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
-- given
  (hHall : ∀ 𝒯 ∈ (rc20_famCylBox 𝒜 ℬ).powerset, 𝒯.card ≤ (𝒯.biUnion (rc33_admOneSidedA n 𝒜 ℬ)).card) :
-- imply
  #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) := by
-- proof
  apply StatMech.Walls.rc33_wall_of_hallOneSidedA n 𝒜 ℬ hHall

/--
[rc33_hallComplete_iff_wall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc33nonlocal.lean)
-/
@[path]
private lemma rc33_hallComplete_iff_wall_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  (∀ 𝒯 ∈ (rc20_famCylBox 𝒜 ℬ).powerset, 𝒯.card ≤ (𝒯.biUnion (fun _ => rc10_reflInter 𝒜 ℬ)).card) ↔ #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) := by
-- proof
  apply StatMech.Walls.rc33_hallComplete_iff_wall 𝒜 ℬ

/--
[rc33_famCylBoxResidue_of_hallOneSidedA](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc33nonlocal.lean)
-/
@[path]
private lemma rc33_famCylBoxResidue_of_hallOneSidedA_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : rc33_HallOneSidedA) :
-- imply
  rc20_FamCylBoxResidue := by
-- proof
  apply StatMech.Walls.rc33_famCylBoxResidue_of_hallOneSidedA h

/--
[rc33_perSupportReflection_of_hallOneSidedA](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc33nonlocal.lean)
-/
@[path]
private lemma rc33_perSupportReflection_of_hallOneSidedA_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : rc33_HallOneSidedA) :
-- imply
  rc20_PerSupportReflection := by
-- proof
  apply StatMech.Walls.rc33_perSupportReflection_of_hallOneSidedA h

/--
[rc33_reimer_closes_of_hallOneSidedA](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc33nonlocal.lean)
-/
@[path]
private lemma rc33_reimer_closes_of_hallOneSidedA_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : rc33_HallOneSidedA) :
-- imply
  rc18_CylBoxReflInter := by
-- proof
  apply StatMech.Walls.rc33_reimer_closes_of_hallOneSidedA h

/--
[rc33_hallOneSidedA_prop_of_bool](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc33nonlocal.lean)
-/
@[path]
private lemma rc33_hallOneSidedA_prop_of_bool_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
-- given
  (h : rc33_hallOneSidedA n 𝒜 ℬ = true) :
-- imply
  ∀ 𝒯 ∈ (rc20_famCylBox 𝒜 ℬ).powerset, 𝒯.card ≤ (𝒯.biUnion (rc33_admOneSidedA n 𝒜 ℬ)).card := by
-- proof
  apply StatMech.Walls.rc33_hallOneSidedA_prop_of_bool n 𝒜 ℬ h

/--
[rc33_hallOneSidedA_fin0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc33nonlocal.lean)
-/
@[path]
private lemma rc33_hallOneSidedA_fin0_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset (Fin 0))} :
-- imply
  rc33_hallOneSidedA 0 𝒜 ℬ = true := by
-- proof
  apply StatMech.Walls.rc33_hallOneSidedA_fin0 𝒜 ℬ

/--
[rc33_hallOneSidedA_fin1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc33nonlocal.lean)
-/
@[path]
private lemma rc33_hallOneSidedA_fin1_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset (Fin 1))} :
-- imply
  rc33_hallOneSidedA 1 𝒜 ℬ = true := by
-- proof
  apply StatMech.Walls.rc33_hallOneSidedA_fin1 𝒜 ℬ

/--
[rc33_hallOneSidedA_fin2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc33nonlocal.lean)
-/
@[path]
private lemma rc33_hallOneSidedA_fin2_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset (Fin 2))} :
-- imply
  rc33_hallOneSidedA 2 𝒜 ℬ = true := by
-- proof
  apply StatMech.Walls.rc33_hallOneSidedA_fin2 𝒜 ℬ

/--
[rc33_wall_fin2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc33nonlocal.lean)
-/
@[path]
private lemma rc33_wall_fin2_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset (Fin 2))} :
-- imply
  #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) := by
-- proof
  apply StatMech.Walls.rc33_wall_fin2 𝒜 ℬ

/--
[rc33_hallOneSidedA_fin3_refuter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc33nonlocal.lean)
-/
@[path]
private lemma rc33_hallOneSidedA_fin3_refuter_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc33_hallOneSidedA 3 rc32_A3 rc32_B3 = true := by
-- proof
  apply StatMech.Walls.rc33_hallOneSidedA_fin3_refuter

/--
[rc33_hallBothSided_fin3_refuted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc33nonlocal.lean)
-/
@[path]
private lemma rc33_hallBothSided_fin3_refuted_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc33_hallBothSided 3 rc32_A3 rc32_B3 = false := by
-- proof
  apply StatMech.Walls.rc33_hallBothSided_fin3_refuted

/--
[rc33_admOneSidedA_proper_fin3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc33nonlocal.lean)
-/
@[path]
private lemma rc33_admOneSidedA_proper_fin3_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc33_admOneSidedA 3 rc32_A3 rc32_B3 {1} ≠ rc10_reflInter rc32_A3 rc32_B3 := by
-- proof
  apply StatMech.Walls.rc33_admOneSidedA_proper_fin3

/--
[rc33_wall_fin3_refuter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc33nonlocal.lean)
-/
@[path]
private lemma rc33_wall_fin3_refuter_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  #(rc20_famCylBox rc32_A3 rc32_B3) ≤ #(rc10_reflInter rc32_A3 rc32_B3) := by
-- proof
  apply StatMech.Walls.rc33_wall_fin3_refuter

/--
[rc33_reimer_nonlocal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc33nonlocal.lean)
-/
@[path]
private lemma rc33_reimer_nonlocal_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (rc33_HallOneSidedA → rc20_PerSupportReflection) ∧ (rc33_HallOneSidedA → rc18_CylBoxReflInter) ∧ (∀ 𝒜 ℬ : Finset (Finset (Fin 2)), #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ)) ∧ (rc33_hallOneSidedA 3 rc32_A3 rc32_B3 = true) ∧ (rc33_hallBothSided 3 rc32_A3 rc32_B3 = false) ∧ (rc33_admOneSidedA 3 rc32_A3 rc32_B3 {1} ≠ rc10_reflInter rc32_A3 rc32_B3) := by
-- proof
  apply StatMech.Walls.rc33_reimer_nonlocal


-- created on 2026-10-23
