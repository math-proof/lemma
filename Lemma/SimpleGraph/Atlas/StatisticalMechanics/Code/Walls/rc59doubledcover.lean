import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.rc59doubledcover
open Finset StatMech StatMech.Walls


/--
[rc59_dblPair_inl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc59doubledcover.lean)
-/
@[path]
private lemma rc59_dblPair_inl_eq
  {n : ℕ}
  {S R : Finset (Fin n)}
  {a : Fin n} :
-- imply
  (Sum.inl a) ∈ rc59_dblPair S R ↔ a ∈ S := by
-- proof
  apply StatMech.Walls.rc59_dblPair_inl S R a

/--
[rc59_dblPair_inr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc59doubledcover.lean)
-/
@[path]
private lemma rc59_dblPair_inr_eq
  {n : ℕ}
  {S R : Finset (Fin n)}
  {a : Fin n} :
-- imply
  (Sum.inr a) ∈ rc59_dblPair S R ↔ a ∈ R := by
-- proof
  apply StatMech.Walls.rc59_dblPair_inr S R a

/--
[rc59_dblPair_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc59doubledcover.lean)
-/
@[path]
private lemma rc59_dblPair_injective_eq
  {n : ℕ} :
-- imply
  Function.Injective (fun p : Finset (Fin n) × Finset (Fin n) => rc59_dblPair p.1 p.2) := by
-- proof
  apply StatMech.Walls.rc59_dblPair_injective

/--
[rc59_doubledCover_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc59doubledcover.lean)
-/
@[path]
private lemma rc59_doubledCover_card_eq
  {n : ℕ}
  {𝒯 : Finset (Finset (Fin n))}
  {f : Finset (Fin n) → Finset (Fin n)} :
-- imply
  (rc59_doubledCover 𝒯 f).card = 𝒯.card := by
-- proof
  apply StatMech.Walls.rc59_doubledCover_card 𝒯 f

/--
[rc59_reimerReflection_inl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc59doubledcover.lean)
-/
@[path]
private lemma rc59_reimerReflection_inl_eq
  {n : ℕ}
  {S K L : Finset (Fin n)}
  {a : Fin n} :
-- imply
  (Sum.inl a) ∈ rc59_reimerReflection S K L ↔ a ∈ S := by
-- proof
  apply StatMech.Walls.rc59_reimerReflection_inl S K L a

/--
[rc59_reimerReflection_inr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc59doubledcover.lean)
-/
@[path]
private lemma rc59_reimerReflection_inr_eq
  {n : ℕ}
  {S K L : Finset (Fin n)}
  {a : Fin n} :
-- imply
  (Sum.inr a) ∈ rc59_reimerReflection S K L ↔ a ∈ rc36_R0 S K L := by
-- proof
  apply StatMech.Walls.rc59_reimerReflection_inr S K L a

/--
[rc59_reimerReflection_mem_reflInter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc59doubledcover.lean)
-/
@[path]
private lemma rc59_reimerReflection_mem_reflInter_eq
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {S K L : Finset (Fin n)}
-- given
  (hKL : Disjoint K L)
  (hKA : ∀ T : Finset (Fin n), T ∩ K = S ∩ K → T ∈ 𝒜)
  (hLB : ∀ T : Finset (Fin n), T ∩ L = S ∩ L → T ∈ ℬ) :
-- imply
  rc36_R0 S K L ∈ rc10_reflInter 𝒜 ℬ := by
-- proof
  apply StatMech.Walls.rc59_reimerReflection_mem_reflInter 𝒜 ℬ hKL hKA hLB

/--
[rc59_nbhd_eq_admOneSidedA](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc59doubledcover.lean)
-/
@[path]
private lemma rc59_nbhd_eq_admOneSidedA_eq
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {S : Finset (Fin n)} :
-- imply
  rc59_nbhd 𝒜 ℬ S = rc33_admOneSidedA n 𝒜 ℬ S := by
-- proof
  apply StatMech.Walls.rc59_nbhd_eq_admOneSidedA 𝒜 ℬ S

/--
[rc59_rightFactor_indep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc59doubledcover.lean)
-/
@[path]
private lemma rc59_rightFactor_indep_eq
  {n : ℕ}
  {ℬ : Finset (Finset (Fin n))}
  {S S' : Finset (Fin n)} :
-- imply
  rc59_rightFactor ℬ = rc59_rightFactor ℬ ∧ (rc59_nbhd 𝒜 ℬ S = rc59_leftFactor 𝒜 S ∩ rc59_rightFactor ℬ ∧ rc59_nbhd 𝒜 ℬ S' = rc59_leftFactor 𝒜 S' ∩ rc59_rightFactor ℬ) := by
-- proof
  apply StatMech.Walls.rc59_rightFactor_indep ℬ S S'

/--
[rc59_reflInter_eq_inter_rightFactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc59doubledcover.lean)
-/
@[path]
private lemma rc59_reflInter_eq_inter_rightFactor_eq
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))} :
-- imply
  rc10_reflInter 𝒜 ℬ = 𝒜 ∩ rc59_rightFactor ℬ := by
-- proof
  apply StatMech.Walls.rc59_reflInter_eq_inter_rightFactor 𝒜 ℬ

/--
[rc59_wall_of_indepHall_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc59doubledcover.lean)
-/
@[path]
private lemma rc59_wall_of_indepHall_pair_eq
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
-- given
  (hHall : ∀ 𝒯 ∈ (rc20_famCylBox 𝒜 ℬ).powerset, 𝒯.card ≤ (𝒯.biUnion (rc59_nbhd 𝒜 ℬ)).card) :
-- imply
  #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) := by
-- proof
  apply StatMech.Walls.rc59_wall_of_indepHall_pair 𝒜 ℬ hHall

/--
[rc59_famCylBoxResidue_of_indepHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc59doubledcover.lean)
-/
@[path]
private lemma rc59_famCylBoxResidue_of_indepHall_eq
  {n : ℕ}
-- given
  (h : rc59_IndepHall) :
-- imply
  rc20_FamCylBoxResidue := by
-- proof
  apply StatMech.Walls.rc59_famCylBoxResidue_of_indepHall h

/--
[rc59_reimerWprobCore_of_indepHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc59doubledcover.lean)
-/
@[path]
private lemma rc59_reimerWprobCore_of_indepHall_eq
  {n : ℕ}
-- given
  (h : rc59_IndepHall) :
-- imply
  ReimerWprobCore := by
-- proof
  apply StatMech.Walls.rc59_reimerWprobCore_of_indepHall h

/--
[rc59_biUnion_nbhd_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc59doubledcover.lean)
-/
@[path]
private lemma rc59_biUnion_nbhd_eq_eq
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {𝒯 : Finset (Finset (Fin n))} :
-- imply
  𝒯.biUnion (rc59_nbhd 𝒜 ℬ) = 𝒯.biUnion (rc33_admOneSidedA n 𝒜 ℬ) := by
-- proof
  apply StatMech.Walls.rc59_biUnion_nbhd_eq 𝒜 ℬ 𝒯

/--
[rc59_indepHall_pair_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc59doubledcover.lean)
-/
@[path]
private lemma rc59_indepHall_pair_iff_eq
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))} :
-- imply
  (∀ 𝒯 ∈ (rc20_famCylBox 𝒜 ℬ).powerset, 𝒯.card ≤ (𝒯.biUnion (rc59_nbhd 𝒜 ℬ)).card) ↔ (∀ 𝒯 ∈ (rc20_famCylBox 𝒜 ℬ).powerset, 𝒯.card ≤ (𝒯.biUnion (rc33_admOneSidedA n 𝒜 ℬ)).card) := by
-- proof
  apply StatMech.Walls.rc59_indepHall_pair_iff 𝒜 ℬ

/--
[rc59_indepHall_fin0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc59doubledcover.lean)
-/
@[path]
private lemma rc59_indepHall_fin0_eq
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin 0))} :
-- imply
  ∀ 𝒯 ∈ (rc20_famCylBox 𝒜 ℬ).powerset, 𝒯.card ≤ (𝒯.biUnion (rc59_nbhd 𝒜 ℬ)).card := by
-- proof
  apply StatMech.Walls.rc59_indepHall_fin0 𝒜 ℬ

/--
[rc59_indepHall_fin1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc59doubledcover.lean)
-/
@[path]
private lemma rc59_indepHall_fin1_eq
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin 1))} :
-- imply
  ∀ 𝒯 ∈ (rc20_famCylBox 𝒜 ℬ).powerset, 𝒯.card ≤ (𝒯.biUnion (rc59_nbhd 𝒜 ℬ)).card := by
-- proof
  apply StatMech.Walls.rc59_indepHall_fin1 𝒜 ℬ

/--
[rc59_indepHall_fin2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc59doubledcover.lean)
-/
@[path]
private lemma rc59_indepHall_fin2_eq
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin 2))} :
-- imply
  ∀ 𝒯 ∈ (rc20_famCylBox 𝒜 ℬ).powerset, 𝒯.card ≤ (𝒯.biUnion (rc59_nbhd 𝒜 ℬ)).card := by
-- proof
  apply StatMech.Walls.rc59_indepHall_fin2 𝒜 ℬ

/--
[rc59_wall_fin2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc59doubledcover.lean)
-/
@[path]
private lemma rc59_wall_fin2_eq
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin 2))} :
-- imply
  #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) := by
-- proof
  apply StatMech.Walls.rc59_wall_fin2 𝒜 ℬ

/--
[rc59_indepHall_fin3_refuter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc59doubledcover.lean)
-/
@[path]
private lemma rc59_indepHall_fin3_refuter_eq
  {n : ℕ} :
-- imply
  ∀ 𝒯 ∈ (rc20_famCylBox rc32_A3 rc32_B3).powerset, 𝒯.card ≤ (𝒯.biUnion (rc59_nbhd rc32_A3 rc32_B3)).card := by
-- proof
  apply StatMech.Walls.rc59_indepHall_fin3_refuter

/--
[rc59_wall_fin3_refuter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc59doubledcover.lean)
-/
@[path]
private lemma rc59_wall_fin3_refuter_eq
  {n : ℕ} :
-- imply
  #(rc20_famCylBox rc32_A3 rc32_B3) ≤ #(rc10_reflInter rc32_A3 rc32_B3) := by
-- proof
  apply StatMech.Walls.rc59_wall_fin3_refuter

/--
[rc59_nbhd_proper_fin3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc59doubledcover.lean)
-/
@[path]
private lemma rc59_nbhd_proper_fin3_eq
  {n : ℕ} :
-- imply
  rc59_nbhd rc32_A3 rc32_B3 {1} ≠ rc10_reflInter rc32_A3 rc32_B3 := by
-- proof
  apply StatMech.Walls.rc59_nbhd_proper_fin3

/--
[rc59_reimerReflection_not_injective_fin3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc59doubledcover.lean)
-/
@[path]
private lemma rc59_reimerReflection_not_injective_fin3_eq
  {n : ℕ} :
-- imply
  ((rc21_boxComp 3 rc32_A3 rc32_B3).biUnion (fun S => (rc21_symmWitComp 3 rc32_A3 rc32_B3 S).image (fun L => symmDiff S L))).card < (rc21_boxComp 3 rc32_A3 rc32_B3).card := by
-- proof
  apply StatMech.Walls.rc59_reimerReflection_not_injective_fin3

/--
[rc59_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc59doubledcover.lean)
-/
@[path]
private lemma rc59_status_eq
  {n : ℕ} :
-- imply
  (rc59_IndepHall → ReimerWprobCore) ∧ (∀ 𝒯 ∈ (rc20_famCylBox rc32_A3 rc32_B3).powerset, 𝒯.card ≤ (𝒯.biUnion (rc59_nbhd rc32_A3 rc32_B3)).card) ∧ (#(rc20_famCylBox rc32_A3 rc32_B3) ≤ #(rc10_reflInter rc32_A3 rc32_B3)) ∧ (rc59_nbhd rc32_A3 rc32_B3 {1} ≠ rc10_reflInter rc32_A3 rc32_B3) := by
-- proof
  apply StatMech.Walls.rc59_status


-- created on 2026-10-23
