import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc27recursion.Part2
open Finset StatMech StatMech.Walls


/--
[rc27_reflInterRecursion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc27recursion.lean)
-/
@[path]
private lemma rc27_reflInterRecursion_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc27_ReflInterRecursion (α := α) := by
-- proof
  apply StatMech.Walls.rc27_reflInterRecursion

/--
[rc27_reflInter_univ_slice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc27recursion.lean)
-/
@[path]
private lemma rc27_reflInter_univ_slice_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {a : α} :
-- imply
  #(rc10_reflInter 𝒜 ℬ) = #(rc14_reflE (univ.erase a) (𝒜.nonMemberSubfamily a) (ℬ.memberSubfamily a)) + #(rc14_reflE (univ.erase a) (𝒜.memberSubfamily a) (ℬ.nonMemberSubfamily a)) := by
-- proof
  apply StatMech.Walls.rc27_reflInter_univ_slice 𝒜 ℬ a

/--
[rc27_boxSlice_sum_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc27recursion.lean)
-/
@[path]
private lemma rc27_boxSlice_sum_false_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  ¬ (#(rc14_boxE (univ : Finset (Fin 1)) ({∅}) ({∅})) ≤ #(rc14_boxE ((univ : Finset (Fin 1)).erase 0) (({∅} : Finset (Finset (Fin 1))).nonMemberSubfamily 0) (({∅} : Finset (Finset (Fin 1))).memberSubfamily 0)) + #(rc14_boxE ((univ : Finset (Fin 1)).erase 0) (({∅} : Finset (Finset (Fin 1))).memberSubfamily 0) (({∅} : Finset (Finset (Fin 1))).nonMemberSubfamily 0))) := by
-- proof
  apply StatMech.Walls.rc27_boxSlice_sum_false

/--
[rc27_boxNesting_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc27recursion.lean)
-/
@[path]
private lemma rc27_boxNesting_false_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  ¬ (rc14_boxE ((univ : Finset (Fin 2)).erase 1) (({∅} : Finset (Finset (Fin 2))).nonMemberSubfamily 1) (({∅} : Finset (Finset (Fin 2))).nonMemberSubfamily 1) ⊆ rc14_boxE ((univ : Finset (Fin 2)).erase 1) (({∅} : Finset (Finset (Fin 2))).memberSubfamily 1) (({∅} : Finset (Finset (Fin 2))).nonMemberSubfamily 1) ∩ rc14_boxE ((univ : Finset (Fin 2)).erase 1) (({∅} : Finset (Finset (Fin 2))).nonMemberSubfamily 1) (({∅} : Finset (Finset (Fin 2))).memberSubfamily 1)) := by
-- proof
  apply StatMech.Walls.rc27_boxNesting_false

/--
[rc27_boxE_le_reflE_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc27recursion.lean)
-/
@[path]
private lemma rc27_boxE_le_reflE_empty_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  #(rc14_boxE (∅ : Finset α) 𝒜 ℬ) ≤ #(rc14_reflE (∅ : Finset α) 𝒜 ℬ) := by
-- proof
  apply StatMech.Walls.rc27_boxE_le_reflE_empty 𝒜 ℬ

/--
[rc27_boxE_le_reflE_of_boxRecursion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc27recursion.lean)
-/
@[path]
private lemma rc27_boxE_le_reflE_of_boxRecursion_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : rc27_BoxSuppRecursion (α := α)) :
-- imply
  ∀ E : Finset α, ∀ 𝒜 ℬ : Finset (Finset α), #(rc14_boxE E 𝒜 ℬ) ≤ #(rc14_reflE E 𝒜 ℬ) := by
-- proof
  apply StatMech.Walls.rc27_boxE_le_reflE_of_boxRecursion h

/--
[rc27_boxSupp_le_reflInter_of_boxRecursion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc27recursion.lean)
-/
@[path]
private lemma rc27_boxSupp_le_reflInter_of_boxRecursion_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
-- given
  (h : rc27_BoxSuppRecursion (α := α)) :
-- imply
  #(rc10_boxSupp 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) := by
-- proof
  apply StatMech.Walls.rc27_boxSupp_le_reflInter_of_boxRecursion h 𝒜 ℬ

/--
[rc27_boxSuppRecursion_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc27recursion.lean)
-/
@[path]
private lemma rc27_boxSuppRecursion_false_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  ¬ rc27_BoxSuppRecursion (α := Fin 1) := by
-- proof
  apply StatMech.Walls.rc27_boxSuppRecursion_false

/--
[rc27_reflInter_recursion_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc27recursion.lean)
-/
@[path]
private lemma rc27_reflInter_recursion_witness_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  #(rc10_reflInter ({∅, {0}, {2}, {0, 2}} : Finset (Finset (Fin 3))) ({{1}, {2}, {1, 2}, {0, 1, 2}})) = 2 + 1 ∧ #(rc14_reflE ((univ : Finset (Fin 3)).erase 2) (({∅, {0}, {2}, {0, 2}} : Finset (Finset (Fin 3))).nonMemberSubfamily 2) (({{1}, {2}, {1, 2}, {0, 1, 2}} : Finset (Finset (Fin 3))).memberSubfamily 2)) = 2 ∧ #(rc14_reflE ((univ : Finset (Fin 3)).erase 2) (({∅, {0}, {2}, {0, 2}} : Finset (Finset (Fin 3))).memberSubfamily 2) (({{1}, {2}, {1, 2}, {0, 1, 2}} : Finset (Finset (Fin 3))).nonMemberSubfamily 2)) = 1 := by
-- proof
  apply StatMech.Walls.rc27_reflInter_recursion_witness

/--
[rc27_reimer_recursion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc27recursion.lean)
-/
@[path]
private lemma rc27_reimer_recursion_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc27_ReflInterRecursion (α := α) ∧ (∀ (𝒜 ℬ : Finset (Finset α)) (a : α), #(rc10_reflInter 𝒜 ℬ) = #(rc14_reflE (univ.erase a) (𝒜.nonMemberSubfamily a) (ℬ.memberSubfamily a)) + #(rc14_reflE (univ.erase a) (𝒜.memberSubfamily a) (ℬ.nonMemberSubfamily a))) ∧ (¬ rc27_BoxSuppRecursion (α := Fin 1)) ∧ (rc27_BoxSuppRecursion (α := α) → ∀ E : Finset α, ∀ 𝒜 ℬ : Finset (Finset α), #(rc14_boxE E 𝒜 ℬ) ≤ #(rc14_reflE E 𝒜 ℬ)) := by
-- proof
  apply StatMech.Walls.rc27_reimer_recursion


-- created on 2026-10-23
