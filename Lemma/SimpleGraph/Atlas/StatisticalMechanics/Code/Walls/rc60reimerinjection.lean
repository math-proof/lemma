import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc60reimerinjection.Part3
open Finset StatMech StatMech.Walls


/--
[rc60_nbhd_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc60reimerinjection.lean)
-/
@[path]
private lemma rc60_nbhd_eq_eq
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {S : Finset (Fin n)} :
-- imply
  rc59_nbhd 𝒜 ℬ S = rc33_admOneSidedA n 𝒜 ℬ S := by
-- proof
  apply StatMech.Walls.rc60_nbhd_eq 𝒜 ℬ S

/--
[rc60_indepHall_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc60reimerinjection.lean)
-/
@[path]
private lemma rc60_indepHall_empty_eq
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))} :
-- imply
  (∅ : Finset (Finset (Fin n))).card ≤ ((∅ : Finset (Finset (Fin n))).biUnion (rc59_nbhd 𝒜 ℬ)).card := by
-- proof
  apply StatMech.Walls.rc60_indepHall_empty 𝒜 ℬ

/--
[rc60_indepHall_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc60reimerinjection.lean)
-/
@[path]
private lemma rc60_indepHall_singleton_eq
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {S : Finset (Fin n)}
-- given
  (hS : S ∈ rc20_famCylBox 𝒜 ℬ) :
-- imply
  ({S} : Finset (Finset (Fin n))).card ≤ (({S} : Finset (Finset (Fin n))).biUnion (rc59_nbhd 𝒜 ℬ)).card := by
-- proof
  apply StatMech.Walls.rc60_indepHall_singleton 𝒜 ℬ hS

/--
[rc60_self_mem_nbhd_of_reflInter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc60reimerinjection.lean)
-/
@[path]
private lemma rc60_self_mem_nbhd_of_reflInter_eq
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {S : Finset (Fin n)}
-- given
  (hS : S ∈ rc10_reflInter 𝒜 ℬ) :
-- imply
  S ∈ rc59_nbhd 𝒜 ℬ S := by
-- proof
  apply StatMech.Walls.rc60_self_mem_nbhd_of_reflInter 𝒜 ℬ hS

/--
[rc60_biUnion_nbhd_subset_reflInter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc60reimerinjection.lean)
-/
@[path]
private lemma rc60_biUnion_nbhd_subset_reflInter_eq
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {𝒯 : Finset (Finset (Fin n))} :
-- imply
  𝒯.biUnion (rc59_nbhd 𝒜 ℬ) ⊆ rc10_reflInter 𝒜 ℬ := by
-- proof
  apply StatMech.Walls.rc60_biUnion_nbhd_subset_reflInter 𝒜 ℬ 𝒯

/--
[rc60_wall_of_boxUnionBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc60reimerinjection.lean)
-/
@[path]
private lemma rc60_wall_of_boxUnionBound_eq
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
-- given
  (h : #(rc20_famCylBox 𝒜 ℬ) ≤ #((rc20_famCylBox 𝒜 ℬ).biUnion (rc59_nbhd 𝒜 ℬ))) :
-- imply
  #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) := by
-- proof
  apply StatMech.Walls.rc60_wall_of_boxUnionBound 𝒜 ℬ h

/--
[rc60_boxUnionBound_of_indepHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc60reimerinjection.lean)
-/
@[path]
private lemma rc60_boxUnionBound_of_indepHall_eq
  {n : ℕ}
  {m : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin m))}
-- given
  (h : rc59_IndepHall) :
-- imply
  #(rc20_famCylBox 𝒜 ℬ) ≤ #((rc20_famCylBox 𝒜 ℬ).biUnion (rc59_nbhd 𝒜 ℬ)) := by
-- proof
  apply StatMech.Walls.rc60_boxUnionBound_of_indepHall h m 𝒜 ℬ

/--
[rc60_famCylBoxResidue_of_boxUnionBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc60reimerinjection.lean)
-/
@[path]
private lemma rc60_famCylBoxResidue_of_boxUnionBound_eq
  {n : ℕ}
-- given
  (h : rc60_BoxUnionBound) :
-- imply
  rc20_FamCylBoxResidue := by
-- proof
  apply StatMech.Walls.rc60_famCylBoxResidue_of_boxUnionBound h

/--
[rc60_reimerWprobCore_of_boxUnionBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc60reimerinjection.lean)
-/
@[path]
private lemma rc60_reimerWprobCore_of_boxUnionBound_eq
  {n : ℕ}
-- given
  (h : rc60_BoxUnionBound) :
-- imply
  ReimerWprobCore := by
-- proof
  apply StatMech.Walls.rc60_reimerWprobCore_of_boxUnionBound h

/--
[rc60_boxUnionBound_of_indepHall_global](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc60reimerinjection.lean)
-/
@[path]
private lemma rc60_boxUnionBound_of_indepHall_global_eq
  {n : ℕ}
-- given
  (h : rc59_IndepHall) :
-- imply
  rc60_BoxUnionBound := by
-- proof
  apply StatMech.Walls.rc60_boxUnionBound_of_indepHall_global h

/--
[rc60_boxUnionBound_fin2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc60reimerinjection.lean)
-/
@[path]
private lemma rc60_boxUnionBound_fin2_eq
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin 2))} :
-- imply
  #(rc20_famCylBox 𝒜 ℬ) ≤ #((rc20_famCylBox 𝒜 ℬ).biUnion (rc59_nbhd 𝒜 ℬ)) := by
-- proof
  apply StatMech.Walls.rc60_boxUnionBound_fin2 𝒜 ℬ

/--
[rc60_boxUnionBound_fin3_refuter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc60reimerinjection.lean)
-/
@[path]
private lemma rc60_boxUnionBound_fin3_refuter_eq
  {n : ℕ} :
-- imply
  #(rc20_famCylBox rc32_A3 rc32_B3) ≤ #((rc20_famCylBox rc32_A3 rc32_B3).biUnion (rc59_nbhd rc32_A3 rc32_B3)) := by
-- proof
  apply StatMech.Walls.rc60_boxUnionBound_fin3_refuter

/--
[rc60_wall_fin3_refuter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc60reimerinjection.lean)
-/
@[path]
private lemma rc60_wall_fin3_refuter_eq
  {n : ℕ} :
-- imply
  #(rc20_famCylBox rc32_A3 rc32_B3) ≤ #(rc10_reflInter rc32_A3 rc32_B3) := by
-- proof
  apply StatMech.Walls.rc60_wall_fin3_refuter

/--
[rc60_reflInter_not_compression_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc60reimerinjection.lean)
-/
@[path]
private lemma rc60_reflInter_not_compression_invariant_eq
  {n : ℕ} :
-- imply
  (rc20_reflInterComp 2 (Down.compression 0 ({{0}} : Finset (Finset (Fin 2)))) ({{1}})).card ≠ (rc20_reflInterComp 2 ({{0}}) ({{1}})).card := by
-- proof
  apply StatMech.Walls.rc60_reflInter_not_compression_invariant

/--
[rc60_hallBothSided_fin3_refuted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc60reimerinjection.lean)
-/
@[path]
private lemma rc60_hallBothSided_fin3_refuted_eq
  {n : ℕ} :
-- imply
  rc33_hallBothSided 3 rc60_A3ex rc60_B3ex = false := by
-- proof
  apply StatMech.Walls.rc60_hallBothSided_fin3_refuted

/--
[rc60_hallOneSidedA_holds_fin3_contrast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc60reimerinjection.lean)
-/
@[path]
private lemma rc60_hallOneSidedA_holds_fin3_contrast_eq
  {n : ℕ} :
-- imply
  rc33_hallOneSidedA 3 rc60_A3ex rc60_B3ex = true := by
-- proof
  apply StatMech.Walls.rc60_hallOneSidedA_holds_fin3_contrast

/--
[rc60_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc60reimerinjection.lean)
-/
@[path]
private lemma rc60_status_eq
  {n : ℕ} :
-- imply
  (rc60_BoxUnionBound → ReimerWprobCore) ∧ (rc59_IndepHall → rc60_BoxUnionBound) ∧ (∀ (𝒜 ℬ : Finset (Finset (Fin 2))), #(rc20_famCylBox 𝒜 ℬ) ≤ #((rc20_famCylBox 𝒜 ℬ).biUnion (rc59_nbhd 𝒜 ℬ))) ∧ (#(rc20_famCylBox rc32_A3 rc32_B3) ≤ #((rc20_famCylBox rc32_A3 rc32_B3).biUnion (rc59_nbhd rc32_A3 rc32_B3))) ∧ (#(rc20_famCylBox rc32_A3 rc32_B3) ≤ #(rc10_reflInter rc32_A3 rc32_B3)) ∧ ((rc20_reflInterComp 2 (Down.compression 0 ({{0}} : Finset (Finset (Fin 2)))) ({{1}})).card ≠ (rc20_reflInterComp 2 ({{0}}) ({{1}})).card) ∧ (rc33_hallBothSided 3 rc60_A3ex rc60_B3ex = false) ∧ (rc33_hallOneSidedA 3 rc60_A3ex rc60_B3ex = true) := by
-- proof
  apply StatMech.Walls.rc60_status


-- created on 2026-10-23
