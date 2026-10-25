import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc_dpairsfiberrecursion
open Finset StatMech StatMech.Walls


/--
[rc_notMem_of_mem_nonMemberSubfamily](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_dpairsfiberrecursion.lean)
-/
@[path]
private lemma rc_notMem_of_mem_nonMemberSubfamily_eq
  [DecidableEq α]
  {A : Finset (Finset α)}
  {i : α}
  {s : Finset α}
-- given
  (hs : s ∈ A.nonMemberSubfamily i) :
-- imply
  i ∉ s := by
-- proof
  apply StatMech.Walls.rc_notMem_of_mem_nonMemberSubfamily A i hs

/--
[rc_notMem_of_mem_memberSubfamily](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_dpairsfiberrecursion.lean)
-/
@[path]
private lemma rc_notMem_of_mem_memberSubfamily_eq
  [DecidableEq α]
  {A : Finset (Finset α)}
  {i : α}
  {s : Finset α}
-- given
  (hs : s ∈ A.memberSubfamily i) :
-- imply
  i ∉ s := by
-- proof
  apply StatMech.Walls.rc_notMem_of_mem_memberSubfamily A i hs

/--
[rc_subfamilies_drop_coordinate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_dpairsfiberrecursion.lean)
-/
@[path]
private lemma rc_subfamilies_drop_coordinate_eq
  [DecidableEq α]
  {A B : Finset (Finset α)}
  {i : α} :
-- imply
  (∀ s ∈ A.nonMemberSubfamily i, i ∉ s) ∧ (∀ s ∈ A.memberSubfamily i, i ∉ s) ∧ (∀ t ∈ B.nonMemberSubfamily i, i ∉ t) ∧ (∀ t ∈ B.memberSubfamily i, i ∉ t) := by
-- proof
  apply StatMech.Walls.rc_subfamilies_drop_coordinate A B i

/--
[rc_fourthFiber_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_dpairsfiberrecursion.lean)
-/
@[path]
private lemma rc_fourthFiber_empty_eq
  [DecidableEq α]
  {A B : Finset (Finset α)}
  {i : α} :
-- imply
  ((A ×ˢ B).filter (fun p => Disjoint p.1 p.2)).filter (fun p => i ∈ p.1 ∧ i ∈ p.2) = ∅ := by
-- proof
  apply StatMech.Walls.rc_fourthFiber_empty A B i

/--
[rc_dpairsCount_fiber_recursion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_dpairsfiberrecursion.lean)
-/
@[path]
private lemma rc_dpairsCount_fiber_recursion_eq
  [DecidableEq α]
  {A B : Finset (Finset α)}
  {i : α} :
-- imply
  dpairsCount A B = dpairsCount (A.nonMemberSubfamily i) (B.nonMemberSubfamily i) + dpairsCount (A.memberSubfamily i) (B.nonMemberSubfamily i) + dpairsCount (A.nonMemberSubfamily i) (B.memberSubfamily i) := by
-- proof
  apply StatMech.Walls.rc_dpairsCount_fiber_recursion A B i

/--
[rc_card_boxDoubled_fiber_recursion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_dpairsfiberrecursion.lean)
-/
@[path]
private lemma rc_card_boxDoubled_fiber_recursion_eq
  [DecidableEq α]
  {A B : Finset (Finset α)}
  {i : α} :
-- imply
  (boxDoubled A B).card = (boxDoubled (A.nonMemberSubfamily i) (B.nonMemberSubfamily i)).card + (boxDoubled (A.memberSubfamily i) (B.nonMemberSubfamily i)).card + (boxDoubled (A.nonMemberSubfamily i) (B.memberSubfamily i)).card := by
-- proof
  apply StatMech.Walls.rc_card_boxDoubled_fiber_recursion A B i


-- created on 2026-10-23
