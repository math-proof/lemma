/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Data.Fintype.Perm
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Logic.Relation
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.GroupTheory.Perm.Support
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.SuccPred
import Mathlib.Order.Fin.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Def.Combinatorics.Enumerative.Nontrivial1234_3412Classes.Part2


namespace MetaMathlibExt

/-- The class count adds over disjoint sets with the second one closed. -/
lemma ntNcl_union {α : Type*} [Finite α] {r : α → α → Prop} {S S' : Set α}
    (hSS' : Disjoint S S')
    (_hS : ∀ x ∈ S, ∀ y, (r x y ∨ r y x) → y ∈ S)
    (hS' : ∀ x ∈ S', ∀ y, (r x y ∨ r y x) → y ∈ S') :
    ntncl r (S ∪ S') = ntncl r S + ntncl r S' := by
  have hFin : Fintype α := Fintype.ofFinite α
  have hSet : Fintype (Set α) := @Set.fintype α hFin
  have hDec : ∀ p : Set α → Prop, DecidablePred p :=
    fun p C => Classical.propDecidable (p C)
  have hFinS : Finite { C : Set α // ∃ x ∈ S, C = ntCls r x ∧ 1 < Nat.card ↥C } :=
    @Finite.of_fintype _ (@Subtype.fintype _ _ (hDec _) hSet)
  have hFinS' : Finite { C : Set α // ∃ x ∈ S', C = ntCls r x ∧ 1 < Nat.card ↥C } :=
    @Finite.of_fintype _ (@Subtype.fintype _ _ (hDec _) hSet)
  have hleft : ∀ a, ntFwd r S S' (Sum.elim (ntBwdL r S S') (ntBwdR r S S') a) = a := by
    intro a
    rcases a with c | c
    · have w := Classical.indefiniteDescription _ c.2
      have hcond : ∃ x ∈ S, (ntBwdL r S S' c).1 = ntCls r x ∧
          1 < Nat.card ↥(ntBwdL r S S' c).1 :=
        ⟨w.1, w.2.1, rfl.trans w.2.2.1, w.2.2.2⟩
      simp only [Sum.elim_inl]
      unfold ntFwd
      rw [dite_eq_left hcond]
      rfl
    · have hneg : ¬∃ x ∈ S, (ntBwdR r S S' c).1 = ntCls r x ∧
          1 < Nat.card ↥(ntBwdR r S S' c).1 := by
        rintro ⟨z, hzS, hCz, -⟩
        have hval : (ntBwdR r S S' c).1 = c.1 := rfl
        rw [hval] at hCz
        have w := Classical.indefiniteDescription _ c.2
        have hcls : ntCls r w.1 = ntCls r z := by rw [← w.2.2.1, ← hCz]
        have hzx : Relation.EqvGen r w.1 z := ntCls_eq.mp hcls
        have hzS' : z ∈ S' := (ntClosed_mem hS' hzx).mp w.2.1
        exact hSS'.notMem_of_mem_left hzS hzS'
      simp only [Sum.elim_inr]
      unfold ntFwd
      rw [dite_eq_right hneg]
      rfl
  have hright : ∀ a, Sum.elim (ntBwdL r S S') (ntBwdR r S S') (ntFwd r S S' a) = a := by
    intro a
    obtain ⟨C, hC⟩ := a
    unfold ntFwd
    split
    · rfl
    · rfl
  have hequiv : ({ C : Set α // ∃ x ∈ S ∪ S', C = ntCls r x ∧ 1 < Nat.card ↥C } ≃
      ({ C : Set α // ∃ x ∈ S, C = ntCls r x ∧ 1 < Nat.card ↥C } ⊕
        { C : Set α // ∃ x ∈ S', C = ntCls r x ∧ 1 < Nat.card ↥C })) :=
    ⟨ntFwd r S S', Sum.elim (ntBwdL r S S') (ntBwdR r S S'), hright, hleft⟩
  have hcard := Nat.card_congr hequiv
  rw [@Nat.card_sum _ _ hFinS hFinS'] at hcard
  unfold ntncl
  exact hcard

/-- Inclusion-exclusion for the class count over closed sets. -/
lemma ntNcl_inter {α : Type*} [Finite α] {r : α → α → Prop} {S S' : Set α}
    (hS : ∀ x ∈ S, ∀ y, (r x y ∨ r y x) → y ∈ S)
    (hS' : ∀ x ∈ S', ∀ y, (r x y ∨ r y x) → y ∈ S') :
    ntncl r (S ∪ S') + ntncl r (S ∩ S') = ntncl r S + ntncl r S' := by
  have hA : ∀ x ∈ S \ S', ∀ y, (r x y ∨ r y x) → y ∈ S \ S' := by
    intro x hx y hxy
    obtain ⟨hxS, hxS'⟩ := hx
    refine ⟨hS x hxS y hxy, ?_⟩
    intro hyS'
    exact hxS' (hS' y hyS' x (or_comm.mp hxy))
  have hB : ∀ x ∈ S ∩ S', ∀ y, (r x y ∨ r y x) → y ∈ S ∩ S' := by
    intro x hx y hxy
    obtain ⟨hxS, hxS'⟩ := hx
    exact ⟨hS x hxS y hxy, hS' x hxS' y hxy⟩
  have hC : ∀ x ∈ S' \ S, ∀ y, (r x y ∨ r y x) → y ∈ S' \ S := by
    intro x hx y hxy
    obtain ⟨hxS', hxS⟩ := hx
    refine ⟨hS' x hxS' y hxy, ?_⟩
    intro hyS
    exact hxS (hS y hyS x (or_comm.mp hxy))
  have dAB : Disjoint (S \ S') (S ∩ S') := by
    rw [Set.disjoint_left]
    intro x hxA hxB
    obtain ⟨-, hxS'⟩ := hxA
    obtain ⟨-, hxS''⟩ := hxB
    exact hxS' hxS''
  have dCB : Disjoint (S' \ S) (S ∩ S') := by
    rw [Set.disjoint_left]
    intro x hxC hxB
    obtain ⟨-, hxS⟩ := hxC
    obtain ⟨hxS'', -⟩ := hxB
    exact hxS hxS''
  have dAS' : Disjoint (S \ S') S' := by
    rw [Set.disjoint_left]
    intro x hxA hxS'
    obtain ⟨-, hxS''⟩ := hxA
    exact hxS'' hxS'
  have e2 : (S' \ S) ∪ (S ∩ S') = S' := by
    rw [Set.inter_comm S S']
    exact Set.sdiff_union_inter S' S
  have e3 : (S \ S') ∪ S' = S ∪ S' := by
    ext x
    simp only [Set.mem_union]
    constructor
    · rintro (⟨hxS, -⟩ | hxS')
      · exact Or.inl hxS
      · exact Or.inr hxS'
    · rintro (hxS | hxS')
      · by_cases hxS' : x ∈ S'
        · exact Or.inr hxS'
        · exact Or.inl ⟨hxS, hxS'⟩
      · exact Or.inr hxS'
  have h1 : ntncl r S = ntncl r (S \ S') + ntncl r (S ∩ S') := by
    have h := ntNcl_union dAB hA hB
    rwa [Set.sdiff_union_inter] at h
  have h2 : ntncl r S' = ntncl r (S' \ S) + ntncl r (S ∩ S') := by
    have h := ntNcl_union dCB hC hB
    rwa [e2] at h
  have h3 : ntncl r (S ∪ S') = ntncl r (S \ S') + ntncl r S' := by
    have h := ntNcl_union dAS' hA hS'
    rwa [e3] at h
  omega

end MetaMathlibExt
