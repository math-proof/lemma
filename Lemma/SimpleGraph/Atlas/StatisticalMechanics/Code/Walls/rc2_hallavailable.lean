import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc2_hallavailable
open Finset Function StatMech ConfigSpace StatMech.Walls


/--
[rc2_hall_available](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_hallavailable.lean)
-/
@[path]
private lemma rc2_hall_available_eq
  [Fintype β]
  [DecidableRel r]
-- given
  (r : α → β → Prop)
  (hHall : ∀ A : Finset α, #A ≤ #{b | ∃ a ∈ A, r a b}) :
-- imply
  ∃ f : α → β, Injective f ∧ ∀ x, r x (f x) := by
-- proof
  apply StatMech.Walls.rc2_hall_available r hHall

/--
[rc2_hall_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_hallavailable.lean)
-/
@[path]
private lemma rc2_hall_iff_eq
  [Fintype β]
  [DecidableRel r]
-- given
  (r : α → β → Prop) :
-- imply
  (∀ A : Finset α, #A ≤ #{b | ∃ a ∈ A, r a b}) ↔ ∃ f : α → β, Injective f ∧ ∀ x, r x (f x) := by
-- proof
  apply StatMech.Walls.rc2_hall_iff r

/--
[rc2_hall_necessary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_hallavailable.lean)
-/
@[path]
private lemma rc2_hall_necessary_eq
  [Fintype β]
  [DecidableRel r]
-- given
  (r : α → β → Prop)
  (h : ∃ f : α → β, Injective f ∧ ∀ x, r x (f x)) :
-- imply
  ∀ A : Finset α, #A ≤ #{b | ∃ a ∈ A, r a b} := by
-- proof
  apply StatMech.Walls.rc2_hall_necessary r h

/--
[rc2_hall_for_swapInjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_hallavailable.lean)
-/
@[path]
private lemma rc2_hall_for_swapInjection_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
  [DecidableRel r]
-- given
  (r : {p : ConfigSpace α × ConfigSpace α // p.1 ∈ disjointOccurrence A B} → (ConfigSpace α × ConfigSpace α) → Prop)
  (hHall : ∀ Aset : Finset {p : ConfigSpace α × ConfigSpace α // p.1 ∈ disjointOccurrence A B}, #Aset ≤ #{b | ∃ a ∈ Aset, r a b}) :
-- imply
  ∃ f : {p : ConfigSpace α × ConfigSpace α // p.1 ∈ disjointOccurrence A B} → (ConfigSpace α × ConfigSpace α), Injective f ∧ ∀ x, r x (f x) := by
-- proof
  apply StatMech.Walls.rc2_hall_for_swapInjection A B r hHall

/--
[rc2_hall_available_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_hallavailable.lean)
-/
@[path]
private lemma rc2_hall_available_nonvacuous_eq
  [Fintype α]
  [DecidableEq α]
  [Fintype β]
  [DecidableEq β] :
-- imply
  ∃ f : β → β, Injective f ∧ ∀ x, (· = ·) x (f x) := by
-- proof
  apply StatMech.Walls.rc2_hall_available_nonvacuous


-- created on 2026-10-23
