import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.rc5_nonvacuity
open Finset StatMech StatMech.Walls


/--
[rc5_reimerCardForm_rbi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_nonvacuity.lean)
-/
@[path]
private lemma rc5_reimerCardForm_rbi_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  poc_ReimerCardForm rbi_A rbi_B := by
-- proof
  apply StatMech.Walls.rc5_reimerCardForm_rbi

/--
[rc5_reimerCardForm_of_disjoint_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_nonvacuity.lean)
-/
@[path]
private lemma rc5_reimerCardForm_of_disjoint_support_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
  {S T : Finset α}
-- given
  (hA : DependsOn A (↑S))
  (hB : DependsOn B (↑T))
  (hST : Disjoint S T) :
-- imply
  poc_ReimerCardForm A B := by
-- proof
  apply StatMech.Walls.rc5_reimerCardForm_of_disjoint_support hA hB hST

/--
[rc5_reimerCardForm_of_box_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_nonvacuity.lean)
-/
@[path]
private lemma rc5_reimerCardForm_of_box_empty_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
-- given
  (hbox : disjointOccurrence A B = ∅) :
-- imply
  poc_ReimerCardForm A B := by
-- proof
  apply StatMech.Walls.rc5_reimerCardForm_of_box_empty hbox

/--
[rc5_reimerCardForm_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_nonvacuity.lean)
-/
@[path]
private lemma rc5_reimerCardForm_one_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace (Fin 1))} :
-- imply
  poc_ReimerCardForm A B := by
-- proof
  apply StatMech.Walls.rc5_reimerCardForm_one A B

/--
[rc5_reimerCardForm_rbi_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_nonvacuity.lean)
-/
@[path]
private lemma rc5_reimerCardForm_rbi_nonvacuous_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  2 ≤ #(univ.filter (fun ω : ConfigSpace (Fin 2) => ω ∈ disjointOccurrence rbi_A rbi_B)) := by
-- proof
  apply StatMech.Walls.rc5_reimerCardForm_rbi_nonvacuous

/--
[rc5_reimerCardForm_nonvacuity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_nonvacuity.lean)
-/
@[path]
private lemma rc5_reimerCardForm_nonvacuity_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  poc_ReimerCardForm rbi_A rbi_B ∧ (∀ {A B : Set (ConfigSpace α)} {S T : Finset α}, DependsOn A (↑S) → DependsOn B (↑T) → Disjoint S T → poc_ReimerCardForm A B) ∧ (∀ {A B : Set (ConfigSpace α)}, disjointOccurrence A B = ∅ → poc_ReimerCardForm A B) ∧ (∀ A B : Set (ConfigSpace (Fin 1)), poc_ReimerCardForm A B) := by
-- proof
  apply StatMech.Walls.rc5_reimerCardForm_nonvacuity

/--
[rc5_slabCard_nonvacuity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_nonvacuity.lean)
-/
@[path]
private lemma rc5_slabCard_nonvacuity_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  poc_SlabCard rbi_A rbi_B ∧ (∀ {A B : Set (ConfigSpace α)} {S T : Finset α}, DependsOn A (↑S) → DependsOn B (↑T) → Disjoint S T → poc_SlabCard A B) ∧ (∀ {A B : Set (ConfigSpace α)}, disjointOccurrence A B = ∅ → poc_SlabCard A B) ∧ (∀ A B : Set (ConfigSpace (Fin 1)), poc_SlabCard A B) := by
-- proof
  apply StatMech.Walls.rc5_slabCard_nonvacuity


-- created on 2026-10-23
