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
import Def.Combinatorics.Enumerative.Nontrivial1234_3412Classes


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
