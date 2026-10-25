import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc3_hallforswapinjection
open Finset Function StatMech ConfigSpace StatMech.Walls


/--
[rc3_hall_for_swapInjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_hallforswapinjection.lean)
-/
@[path]
private lemma rc3_hall_for_swapInjection_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
-- given
  (hHall : ∀ Aset : Finset {p : ConfigSpace α × ConfigSpace α // p.1 ∈ disjointOccurrence A B}, #Aset ≤ #{q | ∃ a ∈ Aset, swapRel A B a q}) :
-- imply
  ∃ f : {p : ConfigSpace α × ConfigSpace α // p.1 ∈ disjointOccurrence A B} → (ConfigSpace α × ConfigSpace α), Injective f ∧ ∀ x, swapRel A B x (f x) := by
-- proof
  apply StatMech.Walls.rc3_hall_for_swapInjection A B hHall

/--
[rc3_hall_for_swapInjection_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_hallforswapinjection.lean)
-/
@[path]
private lemma rc3_hall_for_swapInjection_iff_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)} :
-- imply
  (∀ Aset : Finset {p : ConfigSpace α × ConfigSpace α // p.1 ∈ disjointOccurrence A B}, #Aset ≤ #{q | ∃ a ∈ Aset, swapRel A B a q}) ↔ ∃ f : {p : ConfigSpace α × ConfigSpace α // p.1 ∈ disjointOccurrence A B} → (ConfigSpace α × ConfigSpace α), Injective f ∧ ∀ x, swapRel A B x (f x) := by
-- proof
  apply StatMech.Walls.rc3_hall_for_swapInjection_iff A B

/--
[rc3_hallCond_of_transversal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_hallforswapinjection.lean)
-/
@[path]
private lemma rc3_hallCond_of_transversal_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
-- given
  (h : ∃ f : {p : ConfigSpace α × ConfigSpace α // p.1 ∈ disjointOccurrence A B} → (ConfigSpace α × ConfigSpace α), Injective f ∧ ∀ x, swapRel A B x (f x)) :
-- imply
  ∀ Aset : Finset {p : ConfigSpace α × ConfigSpace α // p.1 ∈ disjointOccurrence A B}, #Aset ≤ #{q | ∃ a ∈ Aset, swapRel A B a q} := by
-- proof
  apply StatMech.Walls.rc3_hallCond_of_transversal A B h

/--
[rc3_hallCond_of_perOrbitCard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_hallforswapinjection.lean)
-/
@[path]
private lemma rc3_hallCond_of_perOrbitCard_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
-- given
  (hpo : PerOrbitCard A B) :
-- imply
  ∀ Aset : Finset {p : ConfigSpace α × ConfigSpace α // p.1 ∈ disjointOccurrence A B}, #Aset ≤ #{q | ∃ a ∈ Aset, swapRel A B a q} := by
-- proof
  apply StatMech.Walls.rc3_hallCond_of_perOrbitCard A B hpo

/--
[rc3_swapInjection_of_transversal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_hallforswapinjection.lean)
-/
@[path]
private lemma rc3_swapInjection_of_transversal_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
-- given
  (f : {p : ConfigSpace α × ConfigSpace α // p.1 ∈ disjointOccurrence A B} → (ConfigSpace α × ConfigSpace α))
  (hfinj : Injective f)
  (hfr : ∀ x, swapRel A B x (f x)) :
-- imply
  r2k_SwapInjection A B := by
-- proof
  apply StatMech.Walls.rc3_swapInjection_of_transversal A B f hfinj hfr

/--
[rc3_swapInjection_of_perOrbitCard'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_hallforswapinjection.lean)
-/
@[path]
private lemma rc3_swapInjection_of_perOrbitCard'_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
-- given
  (hpo : PerOrbitCard A B) :
-- imply
  r2k_SwapInjection A B := by
-- proof
  apply StatMech.Walls.rc3_swapInjection_of_perOrbitCard' A B hpo

/--
[rc3_perOrbitCard_iff_hallCond](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_hallforswapinjection.lean)
-/
@[path]
private lemma rc3_perOrbitCard_iff_hallCond_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)} :
-- imply
  PerOrbitCard A B ↔ ∀ Aset : Finset {p : ConfigSpace α × ConfigSpace α // p.1 ∈ disjointOccurrence A B}, #Aset ≤ #{q | ∃ a ∈ Aset, swapRel A B a q} := by
-- proof
  apply StatMech.Walls.rc3_perOrbitCard_iff_hallCond A B

/--
[rc3_hallCond_rbi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_hallforswapinjection.lean)
-/
@[path]
private lemma rc3_hallCond_rbi_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  ∀ Aset : Finset {p : ConfigSpace (Fin 2) × ConfigSpace (Fin 2) // p.1 ∈ disjointOccurrence rbi_A rbi_B}, #Aset ≤ #{q | ∃ a ∈ Aset, swapRel rbi_A rbi_B a q} := by
-- proof
  apply StatMech.Walls.rc3_hallCond_rbi

/--
[rc3_hall_for_swapInjection_rbi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_hallforswapinjection.lean)
-/
@[path]
private lemma rc3_hall_for_swapInjection_rbi_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  ∃ f : {p : ConfigSpace (Fin 2) × ConfigSpace (Fin 2) // p.1 ∈ disjointOccurrence rbi_A rbi_B} → (ConfigSpace (Fin 2) × ConfigSpace (Fin 2)), Injective f ∧ ∀ x, swapRel rbi_A rbi_B x (f x) := by
-- proof
  apply StatMech.Walls.rc3_hall_for_swapInjection_rbi

/--
[rc3_hallCond_of_disjoint_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_hallforswapinjection.lean)
-/
@[path]
private lemma rc3_hallCond_of_disjoint_support_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
  {S T : Finset α}
-- given
  (hA : DependsOn A (↑S))
  (hB : DependsOn B (↑T))
  (hST : Disjoint S T) :
-- imply
  ∀ Aset : Finset {p : ConfigSpace α × ConfigSpace α // p.1 ∈ disjointOccurrence A B}, #Aset ≤ #{q | ∃ a ∈ Aset, swapRel A B a q} := by
-- proof
  apply StatMech.Walls.rc3_hallCond_of_disjoint_support hA hB hST

/--
[rc3_hallCond_of_box_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_hallforswapinjection.lean)
-/
@[path]
private lemma rc3_hallCond_of_box_empty_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
-- given
  (hbox : disjointOccurrence A B = ∅) :
-- imply
  ∀ Aset : Finset {p : ConfigSpace α × ConfigSpace α // p.1 ∈ disjointOccurrence A B}, #Aset ≤ #{q | ∃ a ∈ Aset, swapRel A B a q} := by
-- proof
  apply StatMech.Walls.rc3_hallCond_of_box_empty hbox


-- created on 2026-10-23
