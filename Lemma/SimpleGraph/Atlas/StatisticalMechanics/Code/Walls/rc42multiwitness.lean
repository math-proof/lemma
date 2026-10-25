import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc42multiwitness.Part6
open Finset StatMech StatMech.Walls


/--
[rc42_traceSlice_disjoint_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc42multiwitness.lean)
-/
@[path]
private lemma rc42_traceSlice_disjoint_of_ne_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {K S S' : Finset α}
-- given
  (h : S ∩ K ≠ S' ∩ K) :
-- imply
  Disjoint (rc35_traceSlice 𝒜 ℬ K S) (rc35_traceSlice 𝒜 ℬ K S') := by
-- proof
  apply StatMech.Walls.rc42_traceSlice_disjoint_of_ne 𝒜 ℬ K S S' h

/--
[rc42_cwits_subset_awitsA](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc42multiwitness.lean)
-/
@[path]
private lemma rc42_cwits_subset_awitsA_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {S : Finset (Fin n)} :
-- imply
  rc42_cwits n 𝒜 ℬ S ⊆ rc35_awitsA n 𝒜 S := by
-- proof
  apply StatMech.Walls.rc42_cwits_subset_awitsA n 𝒜 ℬ S

/--
[rc42_admCovering_subset_admOneSidedA](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc42multiwitness.lean)
-/
@[path]
private lemma rc42_admCovering_subset_admOneSidedA_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {S : Finset (Fin n)} :
-- imply
  rc42_admCovering n 𝒜 ℬ S ⊆ rc33_admOneSidedA n 𝒜 ℬ S := by
-- proof
  apply StatMech.Walls.rc42_admCovering_subset_admOneSidedA n 𝒜 ℬ S

/--
[rc42_admCovering_nonempty_of_mem_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc42multiwitness.lean)
-/
@[path]
private lemma rc42_admCovering_nonempty_of_mem_box_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {S : Finset (Fin n)}
-- given
  (hS : S ∈ rc20_famCylBox 𝒜 ℬ) :
-- imply
  (rc42_admCovering n 𝒜 ℬ S).Nonempty := by
-- proof
  apply StatMech.Walls.rc42_admCovering_nonempty_of_mem_box n 𝒜 ℬ hS

/--
[rc42_biUnionCovering_le_biUnion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc42multiwitness.lean)
-/
@[path]
private lemma rc42_biUnionCovering_le_biUnion_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {𝒯 : Finset (Finset (Fin n))} :
-- imply
  (𝒯.biUnion (rc42_admCovering n 𝒜 ℬ)).card ≤ (𝒯.biUnion (rc33_admOneSidedA n 𝒜 ℬ)).card := by
-- proof
  apply StatMech.Walls.rc42_biUnionCovering_le_biUnion n 𝒜 ℬ 𝒯

/--
[rc42_defectZero_of_hallCovering](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc42multiwitness.lean)
-/
@[path]
private lemma rc42_defectZero_of_hallCovering_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : rc42_HallCovering) :
-- imply
  rc41_DefectZero := by
-- proof
  apply StatMech.Walls.rc42_defectZero_of_hallCovering h

/--
[rc42_reimer_closes_of_hallCovering](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc42multiwitness.lean)
-/
@[path]
private lemma rc42_reimer_closes_of_hallCovering_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : rc42_HallCovering) :
-- imply
  rc18_CylBoxReflInter := by
-- proof
  apply StatMech.Walls.rc42_reimer_closes_of_hallCovering h

/--
[rc42_slice_subset_admCovering](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc42multiwitness.lean)
-/
@[path]
private lemma rc42_slice_subset_admCovering_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {𝒯 : Finset (Finset (Fin n))}
  {K : Finset (Fin n)}
  {S : Finset (Fin n)}
-- given
  (hKw : ∀ S ∈ 𝒯, rc20_traceClass n K S ⊆ 𝒜 ∧ rc20_traceClass n Kᶜ S ⊆ ℬ)
  (hS : S ∈ 𝒯) :
-- imply
  rc35_traceSlice 𝒜 ℬ K S ⊆ rc42_admCovering n 𝒜 ℬ S := by
-- proof
  apply StatMech.Walls.rc42_slice_subset_admCovering n 𝒜 ℬ hKw hS

/--
[rc42_traceImage_le_biUnionCovering](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc42multiwitness.lean)
-/
@[path]
private lemma rc42_traceImage_le_biUnionCovering_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {𝒯 : Finset (Finset (Fin n))}
  {K : Finset (Fin n)}
-- given
  (hKw : ∀ S ∈ 𝒯, rc20_traceClass n K S ⊆ 𝒜 ∧ rc20_traceClass n Kᶜ S ⊆ ℬ) :
-- imply
  (𝒯.image (fun S => S ∩ K)).card ≤ (𝒯.biUnion (rc42_admCovering n 𝒜 ℬ)).card := by
-- proof
  apply StatMech.Walls.rc42_traceImage_le_biUnionCovering n 𝒜 ℬ hKw

/--
[rc42_card_biUnion_traceSlice_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc42multiwitness.lean)
-/
@[path]
private lemma rc42_card_biUnion_traceSlice_eq_sum_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {K : Finset α}
  {𝒯 : Finset (Finset α)} :
-- imply
  ((𝒯.image (fun S => S ∩ K)).biUnion (fun t => rc35_traceSlice 𝒜 ℬ K t)).card = ∑ t ∈ 𝒯.image (fun S => S ∩ K), (rc35_traceSlice 𝒜 ℬ K t).card := by
-- proof
  apply StatMech.Walls.rc42_card_biUnion_traceSlice_eq_sum 𝒜 ℬ K 𝒯

/--
[rc42_traceSliceComp_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc42multiwitness.lean)
-/
@[path]
private lemma rc42_traceSliceComp_eq_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {K S : Finset (Fin n)} :
-- imply
  rc42_traceSliceComp n 𝒜 ℬ K S = rc35_traceSlice 𝒜 ℬ K S := by
-- proof
  apply StatMech.Walls.rc42_traceSliceComp_eq n 𝒜 ℬ K S

/--
[rc42_admCoveringComp_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc42multiwitness.lean)
-/
@[path]
private lemma rc42_admCoveringComp_eq_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {S : Finset (Fin n)} :
-- imply
  rc42_admCoveringComp n 𝒜 ℬ S = rc42_admCovering n 𝒜 ℬ S := by
-- proof
  apply StatMech.Walls.rc42_admCoveringComp_eq n 𝒜 ℬ S

/--
[rc42_hallCovering_prop_of_bool](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc42multiwitness.lean)
-/
@[path]
private lemma rc42_hallCovering_prop_of_bool_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
-- given
  (h : rc42_hallCovering n 𝒜 ℬ = true) :
-- imply
  ∀ 𝒯 ∈ (rc20_famCylBox 𝒜 ℬ).powerset, 𝒯.card ≤ (𝒯.biUnion (rc42_admCovering n 𝒜 ℬ)).card := by
-- proof
  apply StatMech.Walls.rc42_hallCovering_prop_of_bool n 𝒜 ℬ h

/--
[rc42_hallCovering_holds_fin3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc42multiwitness.lean)
-/
@[path]
private lemma rc42_hallCovering_holds_fin3_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc42_hallCovering 3 rc40_Aref rc40_Bref = true := by
-- proof
  apply StatMech.Walls.rc42_hallCovering_holds_fin3

/--
[rc42_hallCovering_holds_A3ex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc42multiwitness.lean)
-/
@[path]
private lemma rc42_hallCovering_holds_A3ex_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc42_hallCovering 3 rc36_A3ex rc36_B3ex = true := by
-- proof
  apply StatMech.Walls.rc42_hallCovering_holds_A3ex

/--
[rc42_admCovering_proper_fin3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc42multiwitness.lean)
-/
@[path]
private lemma rc42_admCovering_proper_fin3_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc42_admCoveringComp 3 ({∅, {0}, {1}}) ({∅, {0}, {0, 2}, {1, 2}, {2}}) ∅ ⊂ rc33_admOneSidedA 3 ({∅, {0}, {1}}) ({∅, {0}, {0, 2}, {1, 2}, {2}}) ∅ := by
-- proof
  apply StatMech.Walls.rc42_admCovering_proper_fin3

/--
[rc42_R0_insufficient_fin3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc42multiwitness.lean)
-/
@[path]
private lemma rc42_R0_insufficient_fin3_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (({{0}, {1}} : Finset (Finset (Fin 3))).biUnion (rc40_R0valuesComp 3 rc40_Aref rc40_Bref)).card < (rc21_boxComp 3 rc40_Aref rc40_Bref).card := by
-- proof
  apply StatMech.Walls.rc42_R0_insufficient_fin3

/--
[rc42_reimer_coveringwitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc42multiwitness.lean)
-/
@[path]
private lemma rc42_reimer_coveringwitness_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (∀ (𝒜 ℬ : Finset (Finset (Fin 3))) (K S S' : Finset (Fin 3)), S ∩ K ≠ S' ∩ K → Disjoint (rc35_traceSlice 𝒜 ℬ K S) (rc35_traceSlice 𝒜 ℬ K S')) ∧ (∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) (S : Finset (Fin n)), rc42_admCovering n 𝒜 ℬ S ⊆ rc33_admOneSidedA n 𝒜 ℬ S) ∧ (rc42_HallCovering → rc41_DefectZero) ∧ (rc42_HallCovering → rc18_CylBoxReflInter) ∧ (rc42_hallCovering 3 rc40_Aref rc40_Bref = true) ∧ ((({{0}, {1}} : Finset (Finset (Fin 3))).biUnion (rc40_R0valuesComp 3 rc40_Aref rc40_Bref)).card < (rc21_boxComp 3 rc40_Aref rc40_Bref).card) ∧ (rc42_admCoveringComp 3 ({∅, {0}, {1}}) ({∅, {0}, {0, 2}, {1, 2}, {2}}) ∅ ⊂ rc33_admOneSidedA 3 ({∅, {0}, {1}}) ({∅, {0}, {0, 2}, {1, 2}, {2}}) ∅) := by
-- proof
  apply StatMech.Walls.rc42_reimer_coveringwitness


-- created on 2026-10-23
