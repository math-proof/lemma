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
import Theorem.Combinatorics.Enumerative.Nontrivial1234_3412Classes


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
