import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.rc36hallmarriage
open Finset StatMech StatMech.Walls


/--
[rc36_R0_inter_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc36hallmarriage.lean)
-/
@[path]
private lemma rc36_R0_inter_left_eq
  [Fintype α]
  [DecidableEq α]
  {S K L : Finset α}
-- given
  (hKL : Disjoint K L) :
-- imply
  rc36_R0 S K L ∩ K = S ∩ K := by
-- proof
  apply StatMech.Walls.rc36_R0_inter_left S K L hKL

/--
[rc36_R0_compl_inter_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc36hallmarriage.lean)
-/
@[path]
private lemma rc36_R0_compl_inter_right_eq
  [Fintype α]
  [DecidableEq α]
  {S K L : Finset α}
-- given
  (hKL : Disjoint K L) :
-- imply
  (rc36_R0 S K L)ᶜ ∩ L = S ∩ L := by
-- proof
  apply StatMech.Walls.rc36_R0_compl_inter_right S K L hKL

/--
[rc36_R0_mem_reflInter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc36hallmarriage.lean)
-/
@[path]
private lemma rc36_R0_mem_reflInter_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {S K L : Finset α}
-- given
  (hKL : Disjoint K L)
  (hKA : ∀ T : Finset α, T ∩ K = S ∩ K → T ∈ 𝒜)
  (hLB : ∀ T : Finset α, T ∩ L = S ∩ L → T ∈ ℬ) :
-- imply
  rc36_R0 S K L ∈ rc10_reflInter 𝒜 ℬ := by
-- proof
  apply StatMech.Walls.rc36_R0_mem_reflInter 𝒜 ℬ hKL hKA hLB

/--
[rc36_R0_mem_traceSlice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc36hallmarriage.lean)
-/
@[path]
private lemma rc36_R0_mem_traceSlice_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {S K L : Finset α}
-- given
  (hKL : Disjoint K L)
  (hKA : ∀ T : Finset α, T ∩ K = S ∩ K → T ∈ 𝒜)
  (hLB : ∀ T : Finset α, T ∩ L = S ∩ L → T ∈ ℬ) :
-- imply
  rc36_R0 S K L ∈ rc35_traceSlice 𝒜 ℬ K S := by
-- proof
  apply StatMech.Walls.rc36_R0_mem_traceSlice 𝒜 ℬ hKL hKA hLB

/--
[rc36_R0_mem_admOneSidedA](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc36hallmarriage.lean)
-/
@[path]
private lemma rc36_R0_mem_admOneSidedA_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {S K L : Finset (Fin n)}
-- given
  (hKL : Disjoint K L)
  (hKA : ∀ T : Finset (Fin n), T ∩ K = S ∩ K → T ∈ 𝒜)
  (hLB : ∀ T : Finset (Fin n), T ∩ L = S ∩ L → T ∈ ℬ) :
-- imply
  rc36_R0 S K L ∈ rc33_admOneSidedA n 𝒜 ℬ S := by
-- proof
  apply StatMech.Walls.rc36_R0_mem_admOneSidedA n 𝒜 ℬ hKL hKA hLB

/--
[rc36_admOneSidedA_nonempty_of_mem_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc36hallmarriage.lean)
-/
@[path]
private lemma rc36_admOneSidedA_nonempty_of_mem_box_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {S : Finset (Fin n)}
-- given
  (hS : S ∈ rc20_famCylBox 𝒜 ℬ) :
-- imply
  (rc33_admOneSidedA n 𝒜 ℬ S).Nonempty := by
-- proof
  apply StatMech.Walls.rc36_admOneSidedA_nonempty_of_mem_box n 𝒜 ℬ hS

/--
[rc36_hallOneSidedA_singletons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc36hallmarriage.lean)
-/
@[path]
private lemma rc36_hallOneSidedA_singletons_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {S : Finset (Fin n)}
-- given
  (hS : S ∈ rc20_famCylBox 𝒜 ℬ) :
-- imply
  ({S} : Finset (Finset (Fin n))).card ≤ (({S} : Finset (Finset (Fin n))).biUnion (rc33_admOneSidedA n 𝒜 ℬ)).card := by
-- proof
  apply StatMech.Walls.rc36_hallOneSidedA_singletons n 𝒜 ℬ hS

/--
[rc36_traceClass_antitone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc36hallmarriage.lean)
-/
@[path]
private lemma rc36_traceClass_antitone_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {K K' : Finset (Fin n)}
  {S : Finset (Fin n)}
-- given
  (hKK' : K ⊆ K') :
-- imply
  rc20_traceClass n K' S ⊆ rc20_traceClass n K S := by
-- proof
  apply StatMech.Walls.rc36_traceClass_antitone n hKK' S

/--
[rc36_awitsA_upward_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc36hallmarriage.lean)
-/
@[path]
private lemma rc36_awitsA_upward_closed_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {𝒜 : Finset (Finset (Fin n))}
  {S : Finset (Fin n)}
  {K K' : Finset (Fin n)}
-- given
  (hK : K ∈ rc35_awitsA n 𝒜 S)
  (hKK' : K ⊆ K') :
-- imply
  K' ∈ rc35_awitsA n 𝒜 S := by
-- proof
  apply StatMech.Walls.rc36_awitsA_upward_closed n 𝒜 S hK hKK'

/--
[rc36_neighbour_empty_singleton_fin3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc36hallmarriage.lean)
-/
@[path]
private lemma rc36_neighbour_empty_singleton_fin3_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc33_admOneSidedA 3 rc36_A3ex rc36_B3ex ∅ = {{1, 2}} := by
-- proof
  apply StatMech.Walls.rc36_neighbour_empty_singleton_fin3

/--
[rc36_neighbour_one_fin3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc36hallmarriage.lean)
-/
@[path]
private lemma rc36_neighbour_one_fin3_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc33_admOneSidedA 3 rc36_A3ex rc36_B3ex {1} = {{1, 2}, {0, 1, 2}} := by
-- proof
  apply StatMech.Walls.rc36_neighbour_one_fin3

/--
[rc36_box_fin3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc36hallmarriage.lean)
-/
@[path]
private lemma rc36_box_fin3_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc21_boxComp 3 rc36_A3ex rc36_B3ex = {∅, {1}} := by
-- proof
  apply StatMech.Walls.rc36_box_fin3

/--
[rc36_minNeighbour_lt_box_fin3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc36hallmarriage.lean)
-/
@[path]
private lemma rc36_minNeighbour_lt_box_fin3_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (rc33_admOneSidedA 3 rc36_A3ex rc36_B3ex ∅).card < (rc21_boxComp 3 rc36_A3ex rc36_B3ex).card := by
-- proof
  apply StatMech.Walls.rc36_minNeighbour_lt_box_fin3

/--
[rc36_neighbour_empty_ssubset_one_fin3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc36hallmarriage.lean)
-/
@[path]
private lemma rc36_neighbour_empty_ssubset_one_fin3_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc33_admOneSidedA 3 rc36_A3ex rc36_B3ex ∅ ⊂ rc33_admOneSidedA 3 rc36_A3ex rc36_B3ex {1} := by
-- proof
  apply StatMech.Walls.rc36_neighbour_empty_ssubset_one_fin3

/--
[rc36_hallOneSidedA_holds_fin3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc36hallmarriage.lean)
-/
@[path]
private lemma rc36_hallOneSidedA_holds_fin3_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc33_hallOneSidedA 3 rc36_A3ex rc36_B3ex = true := by
-- proof
  apply StatMech.Walls.rc36_hallOneSidedA_holds_fin3

/--
[rc36_reimer_defectcounting](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc36hallmarriage.lean)
-/
@[path]
private lemma rc36_reimer_defectcounting_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) {S K L : Finset (Fin n)}, Disjoint K L → (∀ T : Finset (Fin n), T ∩ K = S ∩ K → T ∈ 𝒜) → (∀ T : Finset (Fin n), T ∩ L = S ∩ L → T ∈ ℬ) → rc36_R0 S K L ∈ rc33_admOneSidedA n 𝒜 ℬ S) ∧ (∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) {S : Finset (Fin n)}, S ∈ rc20_famCylBox 𝒜 ℬ → (rc33_admOneSidedA n 𝒜 ℬ S).Nonempty) ∧ (∀ (n : ℕ) (𝒜 : Finset (Finset (Fin n))) (S : Finset (Fin n)) {K K' : Finset (Fin n)}, K ∈ rc35_awitsA n 𝒜 S → K ⊆ K' → K' ∈ rc35_awitsA n 𝒜 S) ∧ (rc33_admOneSidedA 3 rc36_A3ex rc36_B3ex ∅ ⊂ rc33_admOneSidedA 3 rc36_A3ex rc36_B3ex {1}) ∧ ((rc33_admOneSidedA 3 rc36_A3ex rc36_B3ex ∅).card < (rc21_boxComp 3 rc36_A3ex rc36_B3ex).card) ∧ (rc33_hallOneSidedA 3 rc36_A3ex rc36_B3ex = true) := by
-- proof
  apply StatMech.Walls.rc36_reimer_defectcounting


-- created on 2026-10-23
