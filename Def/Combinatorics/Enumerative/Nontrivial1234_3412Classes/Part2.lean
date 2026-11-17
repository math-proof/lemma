/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Logic.Relation
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.GroupTheory.Perm.Support
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Data.Fin.Rev
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Order.Fin.Basic
public import Mathlib.Data.List.GetD
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.Tactic
public import Theorem.Combinatorics.Enumerative.Nontrivial1234_3412Classes

@[expose] public section

namespace MetaMathlibExt

open Classical in
/-- Forward map for the disjoint-union count: split by whether the class meets `S`. -/
noncomputable def ntFwd {α : Type*} (r : α → α → Prop) (S S' : Set α)
    (C : { C : Set α // ∃ x ∈ S ∪ S', C = ntCls r x ∧ 1 < Nat.card ↥C }) :
    ({ C : Set α // ∃ x ∈ S, C = ntCls r x ∧ 1 < Nat.card ↥C } ⊕
      { C : Set α // ∃ x ∈ S', C = ntCls r x ∧ 1 < Nat.card ↥C }) :=
  dite (∃ x ∈ S, C.1 = ntCls r x ∧ 1 < Nat.card ↥C.1)
    (fun h => Sum.inl ⟨C.1, (Classical.indefiniteDescription _ h).1,
      (Classical.indefiniteDescription _ h).2.1,
      (Classical.indefiniteDescription _ h).2.2.1,
      (Classical.indefiniteDescription _ h).2.2.2⟩)
    (fun hno =>
      have hS' : (Classical.indefiniteDescription _ C.2).1 ∈ S' := by
        rcases (Set.mem_union (Classical.indefiniteDescription _ C.2).1 S S').mp
          (Classical.indefiniteDescription _ C.2).2.1 with hS | hS'
        · exact absurd ⟨(Classical.indefiniteDescription _ C.2).1, hS,
            (Classical.indefiniteDescription _ C.2).2.2.1,
            (Classical.indefiniteDescription _ C.2).2.2.2⟩ hno
        · exact hS'
      Sum.inr ⟨C.1, (Classical.indefiniteDescription _ C.2).1, hS',
        (Classical.indefiniteDescription _ C.2).2.2.1,
        (Classical.indefiniteDescription _ C.2).2.2.2⟩)

/-- Backward maps for the disjoint-union count. -/
noncomputable def ntBwdL {α : Type*} (r : α → α → Prop) (S S' : Set α)
    (c : { C : Set α // ∃ x ∈ S, C = ntCls r x ∧ 1 < Nat.card ↥C }) :
    { C : Set α // ∃ x ∈ S ∪ S', C = ntCls r x ∧ 1 < Nat.card ↥C } :=
  ⟨c.1, (Classical.indefiniteDescription _ c.2).1,
    (Set.mem_union _ _ _).mpr
      (Or.inl (Classical.indefiniteDescription _ c.2).2.1),
    (Classical.indefiniteDescription _ c.2).2.2.1,
    (Classical.indefiniteDescription _ c.2).2.2.2⟩

noncomputable def ntBwdR {α : Type*} (r : α → α → Prop) (S S' : Set α)
    (c : { C : Set α // ∃ x ∈ S', C = ntCls r x ∧ 1 < Nat.card ↥C }) :
    { C : Set α // ∃ x ∈ S ∪ S', C = ntCls r x ∧ 1 < Nat.card ↥C } :=
  ⟨c.1, (Classical.indefiniteDescription _ c.2).1,
    (Set.mem_union _ _ _).mpr
      (Or.inr (Classical.indefiniteDescription _ c.2).2.1),
    (Classical.indefiniteDescription _ c.2).2.2.1,
    (Classical.indefiniteDescription _ c.2).2.2.2⟩

end MetaMathlibExt
