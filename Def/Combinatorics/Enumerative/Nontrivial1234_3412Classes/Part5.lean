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
import Theorem.Combinatorics.Enumerative.Nontrivial1234_3412Classes.Part4


namespace MetaMathlibExt

/-- Forward class map for transport. -/
noncomputable def ntMapFwd {α β : Type*} {r : α → α → Prop}
    {r' : β → β → Prop} {f : β → α} (hf : Function.Injective f)
    (hiff : ∀ a b, r' a b ↔ r (f a) (f b))
    (hclosed : ∀ x ∈ Set.range f, ∀ y, (r x y ∨ r y x) → y ∈ Set.range f)
    (S' : Set β)
    (C' : { C' : Set β // ∃ x ∈ S', C' = ntCls r' x ∧ 1 < Nat.card ↥C' }) :
    { C : Set α // ∃ x ∈ f '' S', C = ntCls r x ∧ 1 < Nat.card ↥C } :=
  ⟨f '' C'.1, f (Classical.indefiniteDescription _ C'.2).1,
    Set.mem_image_of_mem f (Classical.indefiniteDescription _ C'.2).2.1,
    ((congrArg (fun C => f '' C)
        (Classical.indefiniteDescription _ C'.2).2.2.1).trans
      (ntCls_map hf hiff hclosed
        (Classical.indefiniteDescription _ C'.2).1).symm),
    by
      rw [ntCard_image hf]
      exact (Classical.indefiniteDescription _ C'.2).2.2.2⟩

/-- Backward class map for transport. -/
noncomputable def ntMapBwd {α β : Type*} {r : α → α → Prop}
    {r' : β → β → Prop} {f : β → α} (hf : Function.Injective f)
    (hiff : ∀ a b, r' a b ↔ r (f a) (f b))
    (hclosed : ∀ x ∈ Set.range f, ∀ y, (r x y ∨ r y x) → y ∈ Set.range f)
    (S' : Set β)
    (C : { C : Set α // ∃ x ∈ f '' S', C = ntCls r x ∧ 1 < Nat.card ↥C }) :
    { C' : Set β // ∃ x ∈ S', C' = ntCls r' x ∧ 1 < Nat.card ↥C' } :=
  ⟨ntCls r' (Classical.indefiniteDescription _
      (ntMem_image (Classical.indefiniteDescription _ C.2).2.1)).1,
    (Classical.indefiniteDescription _
      (ntMem_image (Classical.indefiniteDescription _ C.2).2.1)).1,
    (Classical.indefiniteDescription _
      (ntMem_image (Classical.indefiniteDescription _ C.2).2.1)).2.1,
    rfl,
    by
      have hcardC : 1 < Nat.card ↥C.1 := by
        obtain ⟨-, -, -, hcard⟩ := C.2
        exact hcard
      have himg : C.1 = f '' ntCls r' (Classical.indefiniteDescription _
          (ntMem_image (Classical.indefiniteDescription _ C.2).2.1)).1 :=
        ((Classical.indefiniteDescription _ C.2).2.2.1.trans
          ((congrArg (ntCls r) (Classical.indefiniteDescription _
            (ntMem_image (Classical.indefiniteDescription _ C.2).2.1)).2.2.symm).trans
            (ntCls_map hf hiff hclosed
              (Classical.indefiniteDescription _
                (ntMem_image
                  (Classical.indefiniteDescription _ C.2).2.1)).1)))
      rw [← ntCard_image hf, ← himg]
      exact hcardC⟩

end MetaMathlibExt
