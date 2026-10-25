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
import Def.Combinatorics.Enumerative.Nontrivial1234_3412Classes.Part5


namespace MetaMathlibExt

/-- Transport of the class count along an injective closed-range map. -/
lemma ntNcl_map {α β : Type*} {r : α → α → Prop} {r' : β → β → Prop}
    {f : β → α} (hf : Function.Injective f)
    (hiff : ∀ a b, r' a b ↔ r (f a) (f b))
    (hclosed : ∀ x ∈ Set.range f, ∀ y, (r x y ∨ r y x) → y ∈ Set.range f)
    (S' : Set β) :
    ntncl r (f '' S') = ntncl r' S' := by
  have hleft : ∀ a, ntMapFwd hf hiff hclosed S' (ntMapBwd hf hiff hclosed S' a) = a := by
    intro a
    obtain ⟨C, hC⟩ := a
    apply Subtype.ext
    change f '' (ntMapBwd hf hiff hclosed S' ⟨C, hC⟩).1 = C
    have hval : (ntMapBwd hf hiff hclosed S' ⟨C, hC⟩).1 =
        ntCls r' (Classical.indefiniteDescription _
          (ntMem_image (Classical.indefiniteDescription _ hC).2.1)).1 := rfl
    rw [hval]
    have hC1 : C = ntCls r (Classical.indefiniteDescription _ hC).1 :=
      (Classical.indefiniteDescription _ hC).2.2.1
    have hfb : f (Classical.indefiniteDescription _
        (ntMem_image (Classical.indefiniteDescription _ hC).2.1)).1 =
        (Classical.indefiniteDescription _ hC).1 :=
      (Classical.indefiniteDescription _
        (ntMem_image (Classical.indefiniteDescription _ hC).2.1)).2.2
    exact ((ntCls_map hf hiff hclosed
      (Classical.indefiniteDescription _
        (ntMem_image (Classical.indefiniteDescription _ hC).2.1)).1).symm.trans
      ((congrArg (ntCls r) hfb).trans hC1.symm))
  have hright : ∀ a, ntMapBwd hf hiff hclosed S' (ntMapFwd hf hiff hclosed S' a) = a := by
    intro a
    obtain ⟨C', hC'⟩ := a
    apply Subtype.ext
    change ntCls r' (Classical.indefiniteDescription _
        (ntMem_image (Classical.indefiniteDescription _
          (ntMapFwd hf hiff hclosed S' ⟨C', hC'⟩).2).2.1)).1 = C'
    have hval : (ntMapFwd hf hiff hclosed S' ⟨C', hC'⟩).1 = f '' C' := rfl
    have hC1 : C' = ntCls r' (Classical.indefiniteDescription _ hC').1 :=
      (Classical.indefiniteDescription _ hC').2.2.1
    have hcls : ntCls r' (Classical.indefiniteDescription _
        (ntMem_image (Classical.indefiniteDescription _
          (ntMapFwd hf hiff hclosed S' ⟨C', hC'⟩).2).2.1)).1 = C' := by
      have e : ntCls r (f (Classical.indefiniteDescription _
          (ntMem_image (Classical.indefiniteDescription _
            (ntMapFwd hf hiff hclosed S' ⟨C', hC'⟩).2).2.1)).1) =
          ntCls r (f (Classical.indefiniteDescription _ hC').1) :=
        ((congrArg (ntCls r) (Classical.indefiniteDescription _
          (ntMem_image (Classical.indefiniteDescription _
            (ntMapFwd hf hiff hclosed S' ⟨C', hC'⟩).2).2.1)).2.2).trans
          ((Classical.indefiniteDescription _
            (ntMapFwd hf hiff hclosed S' ⟨C', hC'⟩).2).2.2.1.symm.trans
            ((congrArg (fun C => f '' C) hC1).trans
              (ntCls_map hf hiff hclosed
                (Classical.indefiniteDescription _ hC').1).symm)))
      have heg : Relation.EqvGen r' (Classical.indefiniteDescription _
          (ntMem_image (Classical.indefiniteDescription _
            (ntMapFwd hf hiff hclosed S' ⟨C', hC'⟩).2).2.1)).1
          (Classical.indefiniteDescription _ hC').1 :=
        ntEqvGen_pullback hf hiff hclosed (ntCls_eq.mp e) _ _ rfl rfl
      exact ((ntCls_eq.mpr heg).trans hC1.symm)
    exact hcls
  have hequiv : ({ C : Set α // ∃ x ∈ f '' S', C = ntCls r x ∧ 1 < Nat.card ↥C } ≃
      { C' : Set β // ∃ x ∈ S', C' = ntCls r' x ∧ 1 < Nat.card ↥C' }) :=
    ⟨ntMapBwd hf hiff hclosed S', ntMapFwd hf hiff hclosed S', hleft, hright⟩
  have hcard := Nat.card_congr hequiv
  unfold ntncl
  exact hcard

end MetaMathlibExt
