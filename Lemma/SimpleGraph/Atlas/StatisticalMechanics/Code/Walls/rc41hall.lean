import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc41hall.Part3
open Finset StatMech StatMech.Walls


/--
[rc41_R0cover_inter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc41hall.lean)
-/
@[path]
private lemma rc41_R0cover_inter_eq
  [Fintype α]
  [DecidableEq α]
  {S K : Finset α} :
-- imply
  rc36_R0 S K Kᶜ ∩ K = S ∩ K := by
-- proof
  apply StatMech.Walls.rc41_R0cover_inter S K

/--
[rc41_R0cover_traceEq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc41hall.lean)
-/
@[path]
private lemma rc41_R0cover_traceEq_eq
  [Fintype α]
  [DecidableEq α]
  {S S' K : Finset α}
-- given
  (h : rc36_R0 S K Kᶜ = rc36_R0 S' K Kᶜ) :
-- imply
  S ∩ K = S' ∩ K := by
-- proof
  apply StatMech.Walls.rc41_R0cover_traceEq S S' K h

/--
[rc41_R0cover_mem_admOneSidedA](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc41hall.lean)
-/
@[path]
private lemma rc41_R0cover_mem_admOneSidedA_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {S K : Finset (Fin n)}
-- given
  (hKA : ∀ T : Finset (Fin n), T ∩ K = S ∩ K → T ∈ 𝒜)
  (hKcB : ∀ T : Finset (Fin n), T ∩ Kᶜ = S ∩ Kᶜ → T ∈ ℬ) :
-- imply
  rc36_R0 S K Kᶜ ∈ rc33_admOneSidedA n 𝒜 ℬ S := by
-- proof
  apply StatMech.Walls.rc41_R0cover_mem_admOneSidedA n 𝒜 ℬ hKA hKcB

/--
[rc41_hall_of_commonWitness_distinctTrace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc41hall.lean)
-/
@[path]
private lemma rc41_hall_of_commonWitness_distinctTrace_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {𝒯 : Finset (Finset (Fin n))}
  {K : Finset (Fin n)}
-- given
  (hKA : ∀ S ∈ 𝒯, ∀ T : Finset (Fin n), T ∩ K = S ∩ K → T ∈ 𝒜)
  (hKcB : ∀ S ∈ 𝒯, ∀ T : Finset (Fin n), T ∩ Kᶜ = S ∩ Kᶜ → T ∈ ℬ)
  (hinj : Set.InjOn (fun S => S ∩ K) (𝒯 : Set (Finset (Fin n)))) :
-- imply
  𝒯.card ≤ (𝒯.biUnion (rc33_admOneSidedA n 𝒜 ℬ)).card := by
-- proof
  apply StatMech.Walls.rc41_hall_of_commonWitness_distinctTrace n 𝒜 ℬ hKA hKcB hinj

/--
[rc41_traceImage_le_biUnion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc41hall.lean)
-/
@[path]
private lemma rc41_traceImage_le_biUnion_eq
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
  (𝒯.image (fun S => S ∩ K)).card ≤ (𝒯.biUnion (rc33_admOneSidedA n 𝒜 ℬ)).card := by
-- proof
  apply StatMech.Walls.rc41_traceImage_le_biUnion n 𝒜 ℬ hKA hKcB

/--
[rc41_hallOneSidedA_iff_defectZero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc41hall.lean)
-/
@[path]
private lemma rc41_hallOneSidedA_iff_defectZero_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc33_HallOneSidedA ↔ rc41_DefectZero := by
-- proof
  apply StatMech.Walls.rc41_hallOneSidedA_iff_defectZero

/--
[rc41_reimer_closes_of_defectZero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc41hall.lean)
-/
@[path]
private lemma rc41_reimer_closes_of_defectZero_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : rc41_DefectZero) :
-- imply
  rc18_CylBoxReflInter := by
-- proof
  apply StatMech.Walls.rc41_reimer_closes_of_defectZero h

/--
[rc41_reimer_closes_of_oneSidedInjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc41hall.lean)
-/
@[path]
private lemma rc41_reimer_closes_of_oneSidedInjection_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : rc35_OneSidedInjection) :
-- imply
  rc18_CylBoxReflInter := by
-- proof
  apply StatMech.Walls.rc41_reimer_closes_of_oneSidedInjection h

/--
[rc41_commonWitness_collidingTrace_fin3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc41hall.lean)
-/
@[path]
private lemma rc41_commonWitness_collidingTrace_fin3_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc41_hasCommonCoveringWitness 3 rc40_Aref rc40_Bref {{0}, {1}} = false := by
-- proof
  apply StatMech.Walls.rc41_commonWitness_collidingTrace_fin3

/--
[rc41_hallOneSidedA_holds_fin3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc41hall.lean)
-/
@[path]
private lemma rc41_hallOneSidedA_holds_fin3_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc33_hallOneSidedA 3 rc40_Aref rc40_Bref = true := by
-- proof
  apply StatMech.Walls.rc41_hallOneSidedA_holds_fin3

/--
[rc41_hallBothSided_fails_fin3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc41hall.lean)
-/
@[path]
private lemma rc41_hallBothSided_fails_fin3_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc33_hallBothSided 3 rc32_A3 rc32_B3 = false := by
-- proof
  apply StatMech.Walls.rc41_hallBothSided_fails_fin3

/--
[rc41_reimer_defectcounting](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc41hall.lean)
-/
@[path]
private lemma rc41_reimer_defectcounting_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) {𝒯 : Finset (Finset (Fin n))} {K : Finset (Fin n)}, (∀ S ∈ 𝒯, ∀ T : Finset (Fin n), T ∩ K = S ∩ K → T ∈ 𝒜) → (∀ S ∈ 𝒯, ∀ T : Finset (Fin n), T ∩ Kᶜ = S ∩ Kᶜ → T ∈ ℬ) → Set.InjOn (fun S => S ∩ K) (𝒯 : Set (Finset (Fin n))) → 𝒯.card ≤ (𝒯.biUnion (rc33_admOneSidedA n 𝒜 ℬ)).card) ∧ (∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) {𝒯 : Finset (Finset (Fin n))} {K : Finset (Fin n)}, (∀ S ∈ 𝒯, ∀ T : Finset (Fin n), T ∩ K = S ∩ K → T ∈ 𝒜) → (∀ S ∈ 𝒯, ∀ T : Finset (Fin n), T ∩ Kᶜ = S ∩ Kᶜ → T ∈ ℬ) → (𝒯.image (fun S => S ∩ K)).card ≤ (𝒯.biUnion (rc33_admOneSidedA n 𝒜 ℬ)).card) ∧ (rc33_HallOneSidedA ↔ rc41_DefectZero) ∧ (rc41_DefectZero → rc18_CylBoxReflInter) ∧ (rc41_hasCommonCoveringWitness 3 rc40_Aref rc40_Bref {{0}, {1}} = false) ∧ (rc33_hallOneSidedA 3 rc40_Aref rc40_Bref = true) ∧ (rc33_hallBothSided 3 rc32_A3 rc32_B3 = false) := by
-- proof
  apply StatMech.Walls.rc41_reimer_defectcounting


-- created on 2026-10-23
