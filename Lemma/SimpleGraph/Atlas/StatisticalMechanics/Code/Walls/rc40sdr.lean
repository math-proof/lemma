import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc40sdr.Part3
open Finset StatMech StatMech.Walls


/--
[rc40_L_sdiff_R0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc40sdr.lean)
-/
@[path]
private lemma rc40_L_sdiff_R0_eq
  [Fintype α]
  [DecidableEq α]
  {S K L : Finset α}
-- given
  (hKL : Disjoint K L) :
-- imply
  L \ rc36_R0 S K L = S ∩ L := by
-- proof
  apply StatMech.Walls.rc40_L_sdiff_R0 S K L hKL

/--
[rc40_R0_recovers_covered](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc40sdr.lean)
-/
@[path]
private lemma rc40_R0_recovers_covered_eq
  [Fintype α]
  [DecidableEq α]
  {S K L : Finset α}
-- given
  (hKL : Disjoint K L) :
-- imply
  (rc36_R0 S K L ∩ K) ∪ (L \ rc36_R0 S K L) = S ∩ (K ∪ L) := by
-- proof
  apply StatMech.Walls.rc40_R0_recovers_covered S K L hKL

/--
[rc40_R0_recovers_of_cover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc40sdr.lean)
-/
@[path]
private lemma rc40_R0_recovers_of_cover_eq
  [Fintype α]
  [DecidableEq α]
  {S K L : Finset α}
-- given
  (hKL : Disjoint K L)
  (hcov : K ∪ L = univ) :
-- imply
  (rc36_R0 S K L ∩ K) ∪ (L \ rc36_R0 S K L) = S := by
-- proof
  apply StatMech.Walls.rc40_R0_recovers_of_cover S K L hKL hcov

/--
[rc40_R0_injOn_of_cover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc40sdr.lean)
-/
@[path]
private lemma rc40_R0_injOn_of_cover_eq
  [Fintype α]
  [DecidableEq α]
  {K L : Finset α}
  {S S' : Finset α}
-- given
  (hKL : Disjoint K L)
  (hcov : K ∪ L = univ)
  (h : rc36_R0 S K L = rc36_R0 S' K L) :
-- imply
  S = S' := by
-- proof
  apply StatMech.Walls.rc40_R0_injOn_of_cover K L hKL hcov h

/--
[rc40_coveringPair_of_mem_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc40sdr.lean)
-/
@[path]
private lemma rc40_coveringPair_of_mem_box_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {S : Finset (Fin n)}
-- given
  (hS : S ∈ rc20_famCylBox 𝒜 ℬ) :
-- imply
  ∃ K L : Finset (Fin n), Disjoint K L ∧ K ∪ L = univ ∧ (∀ T : Finset (Fin n), T ∩ K = S ∩ K → T ∈ 𝒜) ∧ (∀ T : Finset (Fin n), T ∩ L = S ∩ L → T ∈ ℬ) := by
-- proof
  apply StatMech.Walls.rc40_coveringPair_of_mem_box n 𝒜 ℬ hS

/--
[rc40_R0_cover_mem_admOneSidedA](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc40sdr.lean)
-/
@[path]
private lemma rc40_R0_cover_mem_admOneSidedA_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {S : Finset (Fin n)}
-- given
  (hS : S ∈ rc20_famCylBox 𝒜 ℬ) :
-- imply
  ∃ K L : Finset (Fin n), Disjoint K L ∧ K ∪ L = univ ∧ rc36_R0 S K L ∈ rc33_admOneSidedA n 𝒜 ℬ S ∧ (rc36_R0 S K L ∩ K) ∪ (L \ rc36_R0 S K L) = S := by
-- proof
  apply StatMech.Walls.rc40_R0_cover_mem_admOneSidedA n 𝒜 ℬ hS

/--
[rc40_R0values_subset_admOneSidedA](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc40sdr.lean)
-/
@[path]
private lemma rc40_R0values_subset_admOneSidedA_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {S : Finset (Fin n)} :
-- imply
  rc40_R0valuesComp n 𝒜 ℬ S ⊆ rc33_admOneSidedA n 𝒜 ℬ S := by
-- proof
  apply StatMech.Walls.rc40_R0values_subset_admOneSidedA n 𝒜 ℬ S

/--
[rc40_box_fin3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc40sdr.lean)
-/
@[path]
private lemma rc40_box_fin3_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc21_boxComp 3 rc40_Aref rc40_Bref = {{0}, {1}} := by
-- proof
  apply StatMech.Walls.rc40_box_fin3

/--
[rc40_R0values_empty_zero_fin3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc40sdr.lean)
-/
@[path]
private lemma rc40_R0values_empty_zero_fin3_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc40_R0valuesComp 3 rc40_Aref rc40_Bref {0} = {∅} := by
-- proof
  apply StatMech.Walls.rc40_R0values_empty_zero_fin3

/--
[rc40_R0values_empty_one_fin3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc40sdr.lean)
-/
@[path]
private lemma rc40_R0values_empty_one_fin3_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc40_R0valuesComp 3 rc40_Aref rc40_Bref {1} = {∅} := by
-- proof
  apply StatMech.Walls.rc40_R0values_empty_one_fin3

/--
[rc40_R0values_biUnion_lt_box_fin3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc40sdr.lean)
-/
@[path]
private lemma rc40_R0values_biUnion_lt_box_fin3_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (({{0}, {1}} : Finset (Finset (Fin 3))).biUnion (rc40_R0valuesComp 3 rc40_Aref rc40_Bref)).card < (rc21_boxComp 3 rc40_Aref rc40_Bref).card := by
-- proof
  apply StatMech.Walls.rc40_R0values_biUnion_lt_box_fin3

/--
[rc40_hallOneSidedA_holds_fin3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc40sdr.lean)
-/
@[path]
private lemma rc40_hallOneSidedA_holds_fin3_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc33_hallOneSidedA 3 rc40_Aref rc40_Bref = true := by
-- proof
  apply StatMech.Walls.rc40_hallOneSidedA_holds_fin3

/--
[rc40_reimer_closes_of_oneSidedInjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc40sdr.lean)
-/
@[path]
private lemma rc40_reimer_closes_of_oneSidedInjection_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : rc35_OneSidedInjection) :
-- imply
  rc18_CylBoxReflInter := by
-- proof
  apply StatMech.Walls.rc40_reimer_closes_of_oneSidedInjection h

/--
[rc40_reimer_r0insufficient](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc40sdr.lean)
-/
@[path]
private lemma rc40_reimer_r0insufficient_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (∀ (S K L : Finset (Fin 3)), Disjoint K L → K ∪ L = univ → (rc36_R0 S K L ∩ K) ∪ (L \ rc36_R0 S K L) = S) ∧ (∀ (K L : Finset (Fin 3)), Disjoint K L → K ∪ L = univ → ∀ {S S' : Finset (Fin 3)}, rc36_R0 S K L = rc36_R0 S' K L → S = S') ∧ (∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) {S : Finset (Fin n)}, S ∈ rc20_famCylBox 𝒜 ℬ → ∃ K L : Finset (Fin n), Disjoint K L ∧ K ∪ L = univ ∧ (∀ T : Finset (Fin n), T ∩ K = S ∩ K → T ∈ 𝒜) ∧ (∀ T : Finset (Fin n), T ∩ L = S ∩ L → T ∈ ℬ)) ∧ (∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) (S : Finset (Fin n)), rc40_R0valuesComp n 𝒜 ℬ S ⊆ rc33_admOneSidedA n 𝒜 ℬ S) ∧ ((({{0}, {1}} : Finset (Finset (Fin 3))).biUnion (rc40_R0valuesComp 3 rc40_Aref rc40_Bref)).card < (rc21_boxComp 3 rc40_Aref rc40_Bref).card) ∧ (rc33_hallOneSidedA 3 rc40_Aref rc40_Bref = true) ∧ (rc35_OneSidedInjection → rc18_CylBoxReflInter) := by
-- proof
  apply StatMech.Walls.rc40_reimer_r0insufficient


-- created on 2026-10-23
