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
import Def.Combinatorics.Enumerative.Nontrivial1234_3412Classes.Part4


namespace MetaMathlibExt

/-- Images under an injection preserve `Nat.card`. -/
lemma ntCard_image {α β : Type*} {f : β → α} (hf : Function.Injective f)
    (s : Set β) : Nat.card ↥(f '' s) = Nat.card ↥s := by
  have hinj : Function.Injective (ntImgFwd f s) := by
    intro a1 a2 h
    have hval : f a1.1 = f a2.1 := congrArg Subtype.val h
    exact Subtype.ext (hf hval)
  have hsurj : Function.Surjective (ntImgFwd f s) := by
    intro b
    obtain ⟨a, haS, hab⟩ := b.2
    exact ⟨⟨a, haS⟩, Subtype.ext hab⟩
  exact (Nat.card_eq_of_bijective (ntImgFwd f s) ⟨hinj, hsurj⟩).symm

/-- Image membership as an explicit existential. -/
lemma ntMem_image {α β : Type*} {f : β → α} {S' : Set β} {x : α}
    (h : x ∈ f '' S') : ∃ b ∈ S', f b = x := h

end MetaMathlibExt
