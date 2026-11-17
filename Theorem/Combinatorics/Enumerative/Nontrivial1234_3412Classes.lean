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
public import Def.Combinatorics.Enumerative.Nontrivial1234_3412Classes

public section

namespace MetaMathlibExt

/-- Membership in a closed set is constant on `EqvGen` classes. -/
lemma ntClosed_mem {α : Type*} {r : α → α → Prop} {S : Set α}
    (hS : ∀ x ∈ S, ∀ y, (r x y ∨ r y x) → y ∈ S)
    {x y : α} (h : Relation.EqvGen r x y) : x ∈ S ↔ y ∈ S := by
  induction h with
  | rel a b hab =>
    constructor
    · intro ha
      exact hS a ha b (Or.inl hab)
    · intro hb
      exact hS b hb a (Or.inr hab)
  | refl a => exact Iff.rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2

end MetaMathlibExt
