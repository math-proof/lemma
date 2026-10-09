import Mathlib
import sympy.Basic

open Topology

/--
[Topology_IsConstructible_mem_of_mem_closure_of_forall_specializes](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Topology_IsConstructible_mem_of_mem_closure_of_forall_specializes.lean)
-/
@[path]
private lemma main
  {X : Type u} [TopologicalSpace X]
  {s : Set X}
  {x : X}
-- given
  (hs : Topology.IsConstructible s)
  (hx : x ∈ closure s)
  (hgen : ∀ y ∈ s, x ⤳ y) :
-- imply
  x ∈ s := by
-- proof
  revert hx hgen
  induction s, hs using BooleanSubalgebra.closure_sdiff_sup_induction with
  | isSublattice =>
    exact ⟨fun s hs t ht ↦ ⟨hs.1.union ht.1, hs.2.union ht.2⟩,
      fun s hs t ht ↦ ⟨hs.1.inter ht.1, hs.2.inter_isOpen ht.2 ht.1⟩⟩
  | bot_mem => exact ⟨isOpen_empty, .empty⟩
  | top_mem => exact ⟨isOpen_univ, .univ⟩
  | sdiff U hU V hV =>
    intro hx hgen
    have hxV : x ∉ V := fun h =>
      (closure_minimal (fun z hz => hz.2) hV.1.isClosed_compl hx) h
    obtain ⟨y, hy⟩ := closure_nonempty_iff.mp ⟨x, hx⟩
    exact ⟨(hgen y hy).mem_open hU.1 hy.1, hxV⟩
  | sup s _ t _ hs' ht' =>
    intro hx hgen
    change x ∈ closure (s ∪ t) at hx
    rw [closure_union] at hx
    rcases hx with hx | hx
    · exact Or.inl (hs' hx fun y hy => hgen y (Or.inl hy))
    · exact Or.inr (ht' hx fun y hy => hgen y (Or.inr hy))


-- created on 2026-10-05
