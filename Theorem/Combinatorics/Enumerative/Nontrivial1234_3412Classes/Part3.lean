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
import Def.Combinatorics.Enumerative.Nontrivial1234_3412Classes.Part3


namespace MetaMathlibExt

/-! ## N3: transporting class counts along an injective map. -/

/-- `EqvGen` maps forward along a relation-preserving map. -/
lemma ntEqvGen_map {α β : Type*} {r : α → α → Prop} {r' : β → β → Prop}
    {f : β → α} (hiff : ∀ a b, r' a b ↔ r (f a) (f b))
    {b w : β} (h : Relation.EqvGen r' b w) : Relation.EqvGen r (f b) (f w) := by
  induction h with
  | rel a c hac => exact Relation.EqvGen.rel _ _ ((hiff a c).mp hac)
  | refl a => exact Relation.EqvGen.refl _
  | symm a c _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans a c d _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

/-- `EqvGen` pulls back along an injective relation-reflecting map. -/
lemma ntEqvGen_pullback {α β : Type*} {r : α → α → Prop}
    {r' : β → β → Prop} {f : β → α} (hf : Function.Injective f)
    (hiff : ∀ a b, r' a b ↔ r (f a) (f b))
    (hclosed : ∀ x ∈ Set.range f, ∀ y, (r x y ∨ r y x) → y ∈ Set.range f)
    {a c : α} (h : Relation.EqvGen r a c) :
    ∀ (u v : β), a = f u → c = f v → Relation.EqvGen r' u v := by
  induction h with
  | rel x y hxy =>
    intro u v ha hc
    subst ha
    subst hc
    exact Relation.EqvGen.rel u v ((hiff u v).mpr hxy)
  | refl x =>
    intro u v ha hc
    have huv : u = v := hf (ha.symm.trans hc)
    subst huv
    exact Relation.EqvGen.refl _
  | symm x y _ ih =>
    intro u v ha hc
    exact Relation.EqvGen.symm v u (ih v u hc ha)
  | trans x y z h1 _ ih1 ih2 =>
    intro u v ha hc
    have hyr : y ∈ Set.range f := (ntClosed_mem hclosed h1).mp ⟨u, ha.symm⟩
    obtain ⟨m, hm⟩ := hyr
    exact Relation.EqvGen.trans u m v (ih1 u m ha hm.symm) (ih2 m v hm.symm hc)

/-- Classes pull back through the image. -/
lemma ntCls_map {α β : Type*} {r : α → α → Prop} {r' : β → β → Prop}
    {f : β → α} (hf : Function.Injective f)
    (hiff : ∀ a b, r' a b ↔ r (f a) (f b))
    (hclosed : ∀ x ∈ Set.range f, ∀ y, (r x y ∨ r y x) → y ∈ Set.range f)
    (b : β) : ntCls r (f b) = f '' ntCls r' b := by
  ext z
  simp only [ntCls, Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · intro hz
    have hzrange : z ∈ Set.range f := (ntClosed_mem hclosed hz).mp ⟨b, rfl⟩
    obtain ⟨w, hw⟩ := hzrange
    refine ⟨w, ?_, hw⟩
    rw [← hw] at hz
    exact ntEqvGen_pullback hf hiff hclosed hz b w rfl rfl
  · rintro ⟨w, hw, rfl⟩
    exact ntEqvGen_map hiff hw

end MetaMathlibExt
