import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.rc43reimer
open Finset StatMech StatMech.Walls


/--
[rc43_famCylBox_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc43reimer.lean)
-/
@[path]
private lemma rc43_famCylBox_symm_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  rc20_famCylBox 𝒜 ℬ = rc20_famCylBox ℬ 𝒜 := by
-- proof
  apply StatMech.Walls.rc43_famCylBox_symm 𝒜 ℬ

/--
[rc43_reflInter_card_transpose](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc43reimer.lean)
-/
@[path]
private lemma rc43_reflInter_card_transpose_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  #(rc10_reflInter 𝒜 ℬ) = #(rc10_reflInter ℬ 𝒜) := by
-- proof
  apply StatMech.Walls.rc43_reflInter_card_transpose 𝒜 ℬ

/--
[rc43_cwits_compl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc43reimer.lean)
-/
@[path]
private lemma rc43_cwits_compl_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {S : Finset (Fin n)} :
-- imply
  (rc42_cwits n 𝒜 ℬ S).image compl = rc42_cwits n ℬ 𝒜 S := by
-- proof
  apply StatMech.Walls.rc43_cwits_compl n 𝒜 ℬ S

/--
[rc43_cwits_card_transpose](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc43reimer.lean)
-/
@[path]
private lemma rc43_cwits_card_transpose_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {S : Finset (Fin n)} :
-- imply
  (rc42_cwits n 𝒜 ℬ S).card = (rc42_cwits n ℬ 𝒜 S).card := by
-- proof
  apply StatMech.Walls.rc43_cwits_card_transpose n 𝒜 ℬ S

/--
[rc43_hall_of_commonCoveringWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc43reimer.lean)
-/
@[path]
private lemma rc43_hall_of_commonCoveringWitness_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {𝒯 : Finset (Finset (Fin n))}
  {K : Finset (Fin n)}
-- given
  (hKA : ∀ S ∈ 𝒯, ∀ T : Finset (Fin n), T ∩ K = S ∩ K → T ∈ 𝒜)
  (hKcB : ∀ S ∈ 𝒯, ∀ T : Finset (Fin n), T ∩ Kᶜ = S ∩ Kᶜ → T ∈ ℬ) :
-- imply
  𝒯.card ≤ (𝒯.biUnion (rc42_admCovering n 𝒜 ℬ)).card := by
-- proof
  apply StatMech.Walls.rc43_hall_of_commonCoveringWitness n 𝒜 ℬ hKA hKcB

/--
[rc43_commonCoveringWitness_generalises_rc41](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc43reimer.lean)
-/
@[path]
private lemma rc43_commonCoveringWitness_generalises_rc41_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {𝒯 : Finset (Finset (Fin n))}
  {K : Finset (Fin n)}
-- given
  (hKA : ∀ S ∈ 𝒯, ∀ T : Finset (Fin n), T ∩ K = S ∩ K → T ∈ 𝒜)
  (hKcB : ∀ S ∈ 𝒯, ∀ T : Finset (Fin n), T ∩ Kᶜ = S ∩ Kᶜ → T ∈ ℬ) :
-- imply
  𝒯.card ≤ (𝒯.biUnion (rc42_admCovering n 𝒜 ℬ)).card := by
-- proof
  apply StatMech.Walls.rc43_commonCoveringWitness_generalises_rc41 n 𝒜 ℬ hKA hKcB

/--
[rc43_hallCovering_of_globalCommonWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc43reimer.lean)
-/
@[path]
private lemma rc43_hallCovering_of_globalCommonWitness_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
-- given
  (h : rc43_GlobalCommonWitness n 𝒜 ℬ) :
-- imply
  ∀ 𝒯 ∈ (rc20_famCylBox 𝒜 ℬ).powerset, 𝒯.card ≤ (𝒯.biUnion (rc42_admCovering n 𝒜 ℬ)).card := by
-- proof
  apply StatMech.Walls.rc43_hallCovering_of_globalCommonWitness n 𝒜 ℬ h

/--
[rc43_famCylBox_le_reflInter_of_globalCommonWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc43reimer.lean)
-/
@[path]
private lemma rc43_famCylBox_le_reflInter_of_globalCommonWitness_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
-- given
  (h : rc43_GlobalCommonWitness n 𝒜 ℬ) :
-- imply
  #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) := by
-- proof
  apply StatMech.Walls.rc43_famCylBox_le_reflInter_of_globalCommonWitness n 𝒜 ℬ h

/--
[rc43_reimer_closes_of_globalCommonWitnessAll](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc43reimer.lean)
-/
@[path]
private lemma rc43_reimer_closes_of_globalCommonWitnessAll_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : rc43_GlobalCommonWitnessAll) :
-- imply
  rc18_CylBoxReflInter := by
-- proof
  apply StatMech.Walls.rc43_reimer_closes_of_globalCommonWitnessAll h

/--
[rc43_globalCommonWitness_prop_of_bool](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc43reimer.lean)
-/
@[path]
private lemma rc43_globalCommonWitness_prop_of_bool_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
-- given
  (h : rc43_globalCommonWitness n 𝒜 ℬ = true) :
-- imply
  rc43_GlobalCommonWitness n 𝒜 ℬ := by
-- proof
  apply StatMech.Walls.rc43_globalCommonWitness_prop_of_bool n 𝒜 ℬ h

/--
[rc43_globalCommonWitness_refuter_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc43reimer.lean)
-/
@[path]
private lemma rc43_globalCommonWitness_refuter_false_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc43_globalCommonWitness 3 rc40_Aref rc40_Bref = false := by
-- proof
  apply StatMech.Walls.rc43_globalCommonWitness_refuter_false

/--
[rc43_globalCommonWitness_univ_fin2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc43reimer.lean)
-/
@[path]
private lemma rc43_globalCommonWitness_univ_fin2_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc43_globalCommonWitness 2 Finset.univ Finset.univ = true := by
-- proof
  apply StatMech.Walls.rc43_globalCommonWitness_univ_fin2

/--
[rc43_residue_named](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc43reimer.lean)
-/
@[path]
private lemma rc43_residue_named_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (rc43_GlobalCommonWitnessAll → rc18_CylBoxReflInter) ∧ (rc43_globalCommonWitness 3 rc40_Aref rc40_Bref = false) ∧ (rc42_hallCovering 3 rc40_Aref rc40_Bref = true) := by
-- proof
  apply StatMech.Walls.rc43_residue_named

/--
[rc43_reimer_symmetry_and_globalwitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc43reimer.lean)
-/
@[path]
private lemma rc43_reimer_symmetry_and_globalwitness_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (∀ (𝒜 ℬ : Finset (Finset (Fin 3))), rc20_famCylBox 𝒜 ℬ = rc20_famCylBox ℬ 𝒜) ∧ (∀ (𝒜 ℬ : Finset (Finset (Fin 3))), #(rc10_reflInter 𝒜 ℬ) = #(rc10_reflInter ℬ 𝒜)) ∧ (∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) {𝒯 : Finset (Finset (Fin n))} {K : Finset (Fin n)}, (∀ S ∈ 𝒯, ∀ T : Finset (Fin n), T ∩ K = S ∩ K → T ∈ 𝒜) → (∀ S ∈ 𝒯, ∀ T : Finset (Fin n), T ∩ Kᶜ = S ∩ Kᶜ → T ∈ ℬ) → 𝒯.card ≤ (𝒯.biUnion (rc42_admCovering n 𝒜 ℬ)).card) ∧ (∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))), rc43_GlobalCommonWitness n 𝒜 ℬ → #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ)) ∧ (rc43_GlobalCommonWitnessAll → rc18_CylBoxReflInter) ∧ (rc43_globalCommonWitness 3 rc40_Aref rc40_Bref = false) ∧ (rc42_hallCovering 3 rc40_Aref rc40_Bref = true) ∧ (rc43_globalCommonWitness 2 Finset.univ Finset.univ = true) := by
-- proof
  apply StatMech.Walls.rc43_reimer_symmetry_and_globalwitness


-- created on 2026-10-23
