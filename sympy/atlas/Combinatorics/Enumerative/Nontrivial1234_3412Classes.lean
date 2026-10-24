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

namespace MetaMathlibExt

/-! ## Basic definitions: the move relation, patterns, class counts. -/

/-- The {1234, 3412}-replacement move on permutations of `Fin n`, exactly the
body of the `Wanted` entry's `let`. -/
private def ntMove (n : ℕ) : Equiv.Perm (Fin n) → Equiv.Perm (Fin n) → Prop :=
  fun σ τ => ∃ i1 i2 i3 i4 : Fin n,
    i1.val < i2.val ∧ i2.val < i3.val ∧ i3.val < i4.val ∧
      σ i1 < σ i2 ∧ σ i2 < σ i3 ∧ σ i3 < σ i4 ∧
      τ i1 = σ i3 ∧ τ i2 = σ i4 ∧ τ i3 = σ i1 ∧ τ i4 = σ i2 ∧
      ∀ j : Fin n, j ≠ i1 → j ≠ i2 → j ≠ i3 → j ≠ i4 → τ j = σ j

/-- A permutation contains a 1234 or a 3412 pattern. -/
private def ntPat (n : ℕ) (σ : Equiv.Perm (Fin n)) : Prop :=
  (∃ i1 i2 i3 i4 : Fin n, i1.val < i2.val ∧ i2.val < i3.val ∧ i3.val < i4.val ∧
    σ i1 < σ i2 ∧ σ i2 < σ i3 ∧ σ i3 < σ i4) ∨
  (∃ i1 i2 i3 i4 : Fin n, i1.val < i2.val ∧ i2.val < i3.val ∧ i3.val < i4.val ∧
    σ i3 < σ i4 ∧ σ i4 < σ i1 ∧ σ i1 < σ i2)

/-- A permutation has an increasing subsequence of length five. -/
private def ntInc5 (n : ℕ) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∃ a b c d e : Fin n, a.val < b.val ∧ b.val < c.val ∧ c.val < d.val ∧
    d.val < e.val ∧ σ a < σ b ∧ σ b < σ c ∧ σ c < σ d ∧ σ d < σ e

/-- Number of nontrivial `EqvGen r` classes meeting the set `S`. -/
private noncomputable def ntncl {α : Type*} (r : α → α → Prop) (S : Set α) : ℕ :=
  Nat.card { C : Set α // ∃ x ∈ S, C = { y | Relation.EqvGen r x y } ∧ 1 < Nat.card ↥C }

/-- The exceptional set: permutations with neither extreme fixed. -/
private def ntE (m : ℕ) : Set (Equiv.Perm (Fin (m + 1))) :=
  { σ | σ 0 ≠ Fin.last m ∧ σ (Fin.last m) ≠ 0 }

/-- Even and odd reference permutations. -/
private def ntEven (n : ℕ) : Equiv.Perm (Fin n) := 1

private def ntOdd (m : ℕ) : Equiv.Perm (Fin (m + 2)) :=
  Equiv.swap ⟨m, by omega⟩ ⟨m + 1, by omega⟩

/-- Reverse-complement of a permutation. -/
private def ntRC {n : ℕ} (σ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n) :=
  (Fin.revPerm : Equiv.Perm (Fin n)) * σ * (Fin.revPerm : Equiv.Perm (Fin n))

/-! ## N2: the `EqvGen` class-counting framework. -/

/-- The `EqvGen r` class of `x`, as a set. -/
private def ntCls {α : Type*} (r : α → α → Prop) (x : α) : Set α :=
  { y | Relation.EqvGen r x y }

/-- Membership in a closed set is constant on `EqvGen` classes. -/
private lemma ntClosed_mem {α : Type*} {r : α → α → Prop} {S : Set α}
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

open Classical in
/-- Forward map for the disjoint-union count: split by whether the class meets `S`. -/
private noncomputable def ntFwd {α : Type*} (r : α → α → Prop) (S S' : Set α)
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
private noncomputable def ntBwdL {α : Type*} (r : α → α → Prop) (S S' : Set α)
    (c : { C : Set α // ∃ x ∈ S, C = ntCls r x ∧ 1 < Nat.card ↥C }) :
    { C : Set α // ∃ x ∈ S ∪ S', C = ntCls r x ∧ 1 < Nat.card ↥C } :=
  ⟨c.1, (Classical.indefiniteDescription _ c.2).1,
    (Set.mem_union _ _ _).mpr
      (Or.inl (Classical.indefiniteDescription _ c.2).2.1),
    (Classical.indefiniteDescription _ c.2).2.2.1,
    (Classical.indefiniteDescription _ c.2).2.2.2⟩

private noncomputable def ntBwdR {α : Type*} (r : α → α → Prop) (S S' : Set α)
    (c : { C : Set α // ∃ x ∈ S', C = ntCls r x ∧ 1 < Nat.card ↥C }) :
    { C : Set α // ∃ x ∈ S ∪ S', C = ntCls r x ∧ 1 < Nat.card ↥C } :=
  ⟨c.1, (Classical.indefiniteDescription _ c.2).1,
    (Set.mem_union _ _ _).mpr
      (Or.inr (Classical.indefiniteDescription _ c.2).2.1),
    (Classical.indefiniteDescription _ c.2).2.2.1,
    (Classical.indefiniteDescription _ c.2).2.2.2⟩

/-- The class count adds over disjoint sets with the second one closed. -/
private lemma ntNcl_union {α : Type*} [Finite α] {r : α → α → Prop} {S S' : Set α}
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
private lemma ntNcl_inter {α : Type*} [Finite α] {r : α → α → Prop} {S S' : Set α}
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

/-- Representative map for the counting lemma. -/
private def ntRepFun {α : Type*} (r : α → α → Prop) (S : Set α) {m : ℕ}
    (x : Fin m → α) (hxS : ∀ k, x k ∈ S)
    (hcard : ∀ k, 1 < Nat.card ↥(ntCls r (x k))) (k : Fin m) :
    { C : Set α // ∃ x ∈ S, C = ntCls r x ∧ 1 < Nat.card ↥C } :=
  ⟨ntCls r (x k), x k, hxS k, rfl, hcard k⟩

/-! ## N3: transporting class counts along an injective map. -/

/-- `EqvGen` maps forward along a relation-preserving map. -/
private lemma ntEqvGen_map {α β : Type*} {r : α → α → Prop} {r' : β → β → Prop}
    {f : β → α} (hiff : ∀ a b, r' a b ↔ r (f a) (f b))
    {b w : β} (h : Relation.EqvGen r' b w) : Relation.EqvGen r (f b) (f w) := by
  induction h with
  | rel a c hac => exact Relation.EqvGen.rel _ _ ((hiff a c).mp hac)
  | refl a => exact Relation.EqvGen.refl _
  | symm a c _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans a c d _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

/-- `EqvGen` pulls back along an injective relation-reflecting map. -/
private lemma ntEqvGen_pullback {α β : Type*} {r : α → α → Prop}
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
private lemma ntCls_map {α β : Type*} {r : α → α → Prop} {r' : β → β → Prop}
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

/-- Forward map on image subtypes. -/
private def ntImgFwd {α β : Type*} (f : β → α) (s : Set β) (a : ↥s) : ↥(f '' s) :=
  ⟨f a.1, a.1, a.2, rfl⟩

/-- Images under an injection preserve `Nat.card`. -/
private lemma ntCard_image {α β : Type*} {f : β → α} (hf : Function.Injective f)
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
private lemma ntMem_image {α β : Type*} {f : β → α} {S' : Set β} {x : α}
    (h : x ∈ f '' S') : ∃ b ∈ S', f b = x := h

/-- Forward class map for transport. -/
private noncomputable def ntMapFwd {α β : Type*} {r : α → α → Prop}
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
private noncomputable def ntMapBwd {α β : Type*} {r : α → α → Prop}
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

/-- Transport of the class count along an injective closed-range map. -/
private lemma ntNcl_map {α β : Type*} {r : α → α → Prop} {r' : β → β → Prop}
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

/-! ## N4: the point-insertion map for permutations. -/

/-- Forward map of point insertion. -/
private def ntInsFwd {m : ℕ} (p v : Fin (m + 1)) (ρ : Equiv.Perm (Fin m)) :
    Fin (m + 1) → Fin (m + 1) :=
  Fin.insertNth p v (fun i => v.succAbove (ρ i))

/-- Backward map of point insertion. -/
private def ntInsBwd {m : ℕ} (p v : Fin (m + 1)) (ρ : Equiv.Perm (Fin m)) :
    Fin (m + 1) → Fin (m + 1) :=
  Fin.insertNth v p (fun j => p.succAbove (ρ.symm j))

/-- Inserting a point into a permutation. -/
private def ntIns {m : ℕ} (p v : Fin (m + 1)) (ρ : Equiv.Perm (Fin m)) :
    Equiv.Perm (Fin (m + 1)) :=
  ⟨ntInsFwd p v ρ, ntInsBwd p v ρ,
    fun x => by
      by_cases hxp : x = p
      · subst hxp
        simp only [ntInsFwd, ntInsBwd, Fin.insertNth_apply_same]
      · obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq_iff.mpr hxp
        subst hi
        simp only [ntInsFwd, ntInsBwd, Fin.insertNth_apply_succAbove,
          Equiv.symm_apply_apply],
    fun x => by
      by_cases hxv : x = v
      · subst hxv
        simp only [ntInsFwd, ntInsBwd, Fin.insertNth_apply_same]
      · obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq_iff.mpr hxv
        subst hj
        simp only [ntInsFwd, ntInsBwd, Fin.insertNth_apply_succAbove,
          Equiv.apply_symm_apply]⟩

/-- Permutations fixing the left extreme value. -/
private def ntA (k : ℕ) : Set (Equiv.Perm (Fin (k + 1))) :=
  {σ | σ 0 = Fin.last k}

/-- Permutations fixing the right extreme value. -/
private def ntB (k : ℕ) : Set (Equiv.Perm (Fin (k + 1))) :=
  {σ | σ (Fin.last k) = 0}

/-- The class count over the left-extreme set equals the count one size down. -/
private lemma ntNcl_A {m : ℕ} :
    ntncl (ntMove (m + 2)) (ntA (m + 1)) = ntncl (ntMove (m + 1)) Set.univ := by
  have hf : Function.Injective (ntIns (0 : Fin (m + 2)) (Fin.last (m + 1))) :=
    ntIns_injective _ _
  have hiff : ∀ a b, ntMove (m + 1) a b ↔
      ntMove (m + 2) (ntIns (0 : Fin (m + 2)) (Fin.last (m + 1)) a)
        (ntIns (0 : Fin (m + 2)) (Fin.last (m + 1)) b) := by
    intro a b
    exact ⟨ntMove_ins _ _, ntMove_descent_zero_last (m := m + 1)⟩
  have hclosed : ∀ x ∈ Set.range (ntIns (0 : Fin (m + 2)) (Fin.last (m + 1))), ∀ y,
      (ntMove (m + 2) x y ∨ ntMove (m + 2) y x) →
        y ∈ Set.range (ntIns (0 : Fin (m + 2)) (Fin.last (m + 1))) := by
    intro x hx y hxy
    obtain ⟨ρ, rfl⟩ := hx
    have hx0 : (ntIns (0 : Fin (m + 2)) (Fin.last (m + 1)) ρ) 0 = Fin.last (m + 1) :=
      ntIns_apply_same _ _ _
    have hy0 : y 0 = Fin.last (m + 1) := ntMove_inert_zero hx0 hxy
    obtain ⟨ρ', rfl⟩ := ntIns_exists _ _ y hy0
    exact ⟨ρ', rfl⟩
  have hmap := ntNcl_map hf hiff hclosed Set.univ
  rw [ntRange_A] at hmap
  exact hmap

/-- The class count over the right-extreme set equals the count one size down. -/
private lemma ntNcl_B {k : ℕ} :
    ntncl (ntMove (k + 1)) (ntB k) = ntncl (ntMove k) Set.univ := by
  have hf : Function.Injective (ntIns (Fin.last k) (0 : Fin (k + 1))) :=
    ntIns_injective _ _
  have hiff : ∀ a b, ntMove k a b ↔
      ntMove (k + 1) (ntIns (Fin.last k) (0 : Fin (k + 1)) a)
        (ntIns (Fin.last k) (0 : Fin (k + 1)) b) := by
    intro a b
    exact ⟨ntMove_ins _ _, ntMove_descent_last_zero (m := k)⟩
  have hclosed :
      ∀ x ∈ Set.range (ntIns (Fin.last k) (0 : Fin (k + 1))), ∀ y,
      (ntMove (k + 1) x y ∨ ntMove (k + 1) y x) →
        y ∈ Set.range (ntIns (Fin.last k) (0 : Fin (k + 1))) := by
    intro x hx y hxy
    obtain ⟨ρ, rfl⟩ := hx
    have hx0 : (ntIns (Fin.last k) (0 : Fin (k + 1)) ρ) (Fin.last k) = 0 :=
      ntIns_apply_same _ _ _
    have hy0 : y (Fin.last k) = 0 := ntMove_inert_last hx0 hxy
    obtain ⟨ρ', rfl⟩ := ntIns_exists _ _ y hy0
    exact ⟨ρ', rfl⟩
  have hmap := ntNcl_map hf hiff hclosed Set.univ
  rw [ntRange_B] at hmap
  exact hmap

/-- The two-step count recursion. -/
private lemma ntCount_recursion (m : ℕ) :
    ntncl (ntMove (m + 2)) Set.univ + ntncl (ntMove m) Set.univ =
      2 * ntncl (ntMove (m + 1)) Set.univ + ntncl (ntMove (m + 2)) (ntE (m + 1)) := by
  have hAB : ∀ x ∈ ntA (m + 1) ∪ ntB (m + 1), ∀ y,
      (ntMove (m + 2) x y ∨ ntMove (m + 2) y x) → y ∈ ntA (m + 1) ∪ ntB (m + 1) := by
    intro x hx y hxy
    rcases hx with hx | hx
    · exact Or.inl (ntA_closed x hx y hxy)
    · exact Or.inr (ntB_closed x hx y hxy)
  have hdisj : Disjoint (ntE (m + 1)) (ntA (m + 1) ∪ ntB (m + 1)) := by
    rw [Set.disjoint_left]
    intro σ hE hn
    rcases hn with h | h
    · exact hE.1 h
    · exact hE.2 h
  have hunion : ntE (m + 1) ∪ (ntA (m + 1) ∪ ntB (m + 1)) = Set.univ := by
    ext σ
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    by_cases h0 : σ 0 = Fin.last (m + 1)
    · exact Or.inr (Or.inl h0)
    · by_cases hl : σ (Fin.last (m + 1)) = 0
      · exact Or.inr (Or.inr hl)
      · exact Or.inl ⟨h0, hl⟩
  have step1 := ntNcl_union hdisj (ntE_closed (m := m)) hAB
  rw [hunion] at step1
  have step2 := ntNcl_inter (ntA_closed (m := m)) (ntB_closed (m := m))
  have hI : ntncl (ntMove (m + 2)) (ntA (m + 1) ∩ ntB (m + 1)) =
      ntncl (ntMove m) Set.univ := by
    have hf : Function.Injective (ntIns (0 : Fin (m + 2)) (Fin.last (m + 1))) :=
      ntIns_injective _ _
    have hiff : ∀ a b, ntMove (m + 1) a b ↔
        ntMove (m + 2) (ntIns (0 : Fin (m + 2)) (Fin.last (m + 1)) a)
          (ntIns (0 : Fin (m + 2)) (Fin.last (m + 1)) b) := by
      intro a b
      exact ⟨ntMove_ins _ _, ntMove_descent_zero_last (m := m + 1)⟩
    have hclosed :
        ∀ x ∈ Set.range (ntIns (0 : Fin (m + 2)) (Fin.last (m + 1))), ∀ y,
        (ntMove (m + 2) x y ∨ ntMove (m + 2) y x) →
          y ∈ Set.range (ntIns (0 : Fin (m + 2)) (Fin.last (m + 1))) := by
      intro x hx y hxy
      obtain ⟨ρ, rfl⟩ := hx
      have hx0 : (ntIns (0 : Fin (m + 2)) (Fin.last (m + 1)) ρ) 0 =
          Fin.last (m + 1) := ntIns_apply_same _ _ _
      have hy0 : y 0 = Fin.last (m + 1) := ntMove_inert_zero hx0 hxy
      obtain ⟨ρ', rfl⟩ := ntIns_exists _ _ y hy0
      exact ⟨ρ', rfl⟩
    have hmap := ntNcl_map hf hiff hclosed (ntB m)
    have hBdown : ntncl (ntMove (m + 1)) (ntB m) = ntncl (ntMove m) Set.univ :=
      ntNcl_B (k := m)
    rw [ntInter_AB, hmap, hBdown]
  have hA := ntNcl_A (m := m)
  have hB : ntncl (ntMove (m + 2)) (ntB (m + 1)) =
      ntncl (ntMove (m + 1)) Set.univ := ntNcl_B (k := m + 1)
  omega

/-- The two-block decreasing function: low block reverses `[0, j)`, high block
reverses `[j, n)` (all on values). -/
private def ntBetaFun (n j : ℕ) (hj : j + 1 ≤ n) (i : Fin n) : Fin n :=
  dite (i.val < j) (fun _ => ⟨j - 1 - i.val, by omega⟩)
    (fun _ => ⟨n + j - 1 - i.val, by have hi := i.is_lt; omega⟩)

/-- Value characterization of the two-block function. -/
private lemma ntBetaFun_val {n j : ℕ} (hj : j + 1 ≤ n) (i : Fin n) :
    (ntBetaFun n j hj i).val =
      if i.val < j then j - 1 - i.val else n + j - 1 - i.val := by
  unfold ntBetaFun
  by_cases h : i.val < j
  · rw [dite_eq_left h, ite_eq_left h]
  · rw [dite_eq_right h, ite_eq_right h]

/-- The two-block function is an involution. -/
private lemma ntBeta_invol {n j : ℕ} (hj : j + 1 ≤ n) (i : Fin n) :
    ntBetaFun n j hj (ntBetaFun n j hj i) = i := by
  have hi := i.is_lt
  apply Fin.ext_iff.mpr
  rw [ntBetaFun_val, ntBetaFun_val]
  by_cases h : i.val < j
  · rw [ite_eq_left h, ite_eq_left (by omega)]
    omega
  · rw [ite_eq_right h, ite_eq_right (by omega)]
    omega

/-- The two-block permutation. -/
private def ntBeta (n j : ℕ) (hj : j + 1 ≤ n) : Equiv.Perm (Fin n) :=
  Function.Involutive.toPerm (ntBetaFun n j hj) (fun i => ntBeta_invol hj i)

/-- The family obtained by composing the two-block permutation with one swap. -/
private def ntT (n j : ℕ) (hj : j + 1 ≤ n) : Set (Equiv.Perm (Fin n)) :=
  {κ | ∃ P Q : Fin n, P ≠ Q ∧ κ = ntBeta n j hj * Equiv.swap P Q}

/-- The patterned part of the swap family. -/
private def ntK (n j : ℕ) (hj : j + 1 ≤ n) : Set (Equiv.Perm (Fin n)) :=
  ntT n j hj ∩ {σ | ntPat n σ}

/-- The generic patterned part: extreme-avoiding patterns outside every `K`. -/
private def ntG (k : ℕ) : Set (Equiv.Perm (Fin (k + 1))) :=
  {σ | σ ∈ ntE k ∧ ntPat (k + 1) σ ∧
    ∀ j : ℕ, ∀ hj : j + 1 ≤ k + 1, σ ∉ ntK (k + 1) j hj}

/-- Value formula for the two-block permutation. -/
private lemma ntBeta_val {n j : ℕ} (hj : j + 1 ≤ n) (i : Fin n) :
    ((ntBeta n j hj) i).val =
      if i.val < j then j - 1 - i.val else n + j - 1 - i.val := by
  have e : (ntBeta n j hj) i = ntBetaFun n j hj i := rfl
  rw [e, ntBetaFun_val]

/-- An increasing value pair in `beta` forces low then high blocks. -/
private lemma ntBeta_force {n j : ℕ} (hj : j + 1 ≤ n) {x y : Fin n}
    (hxy : x.val < y.val) (h : (ntBeta n j hj) x < (ntBeta n j hj) y) :
    x.val < j ∧ j ≤ y.val := by
  rw [Fin.lt_def, ntBeta_val hj, ntBeta_val hj] at h
  by_cases hx : x.val < j
  · by_cases hyj : y.val < j
    · rw [ite_eq_left hx, ite_eq_left hyj] at h
      omega
    · exact ⟨hx, not_lt.mp hyj⟩
  · by_cases hyj : y.val < j
    · omega
    · rw [ite_eq_right hx, ite_eq_right hyj] at h
      omega

/-- A decreasing value pair in `beta` forces high or low blocks. -/
private lemma ntBeta_force_gt {n j : ℕ} (hj : j + 1 ≤ n) {x y : Fin n}
    (_hxy : x.val < y.val) (h : (ntBeta n j hj) y < (ntBeta n j hj) x) :
    j ≤ x.val ∨ y.val < j := by
  by_cases hx : x.val < j
  · by_cases hyj : y.val < j
    · exact Or.inr hyj
    · exfalso
      have hlt : (ntBeta n j hj) x < (ntBeta n j hj) y := by
        rw [Fin.lt_def, ntBeta_val hj, ntBeta_val hj, ite_eq_left hx, ite_eq_right hyj]
        have := y.is_lt
        omega
      exact absurd (lt_trans hlt h) (lt_irrefl _)
  · exact Or.inl (not_lt.mp hx)

/-- The two-block permutation has no increasing triple. -/
private lemma ntBeta_no123 {n j : ℕ} (hj : j + 1 ≤ n) :
    ¬∃ a b c : Fin n, a.val < b.val ∧ b.val < c.val ∧
      (ntBeta n j hj) a < (ntBeta n j hj) b ∧
      (ntBeta n j hj) b < (ntBeta n j hj) c := by
  rintro ⟨a, b, c, hab, hbc, h1, h2⟩
  obtain ⟨ha, hbhi⟩ := ntBeta_force hj hab h1
  obtain ⟨hb, -⟩ := ntBeta_force hj hbc h2
  omega

/-- The two-block permutation has no 231 triple. -/
private lemma ntBeta_no231 {n j : ℕ} (hj : j + 1 ≤ n) :
    ¬∃ a b c : Fin n, a.val < b.val ∧ b.val < c.val ∧
      (ntBeta n j hj) c < (ntBeta n j hj) a ∧
      (ntBeta n j hj) a < (ntBeta n j hj) b := by
  rintro ⟨a, b, c, hab, hbc, hca, habv⟩
  have hac : a.val < c.val := lt_trans hab hbc
  obtain ⟨ha, hbhi⟩ := ntBeta_force hj hab habv
  rcases ntBeta_force_gt hj hac hca with ha' | hc
  · omega
  · omega

/-- The two-block permutation has no 312 triple. -/
private lemma ntBeta_no312 {n j : ℕ} (hj : j + 1 ≤ n) :
    ¬∃ a b c : Fin n, a.val < b.val ∧ b.val < c.val ∧
      (ntBeta n j hj) b < (ntBeta n j hj) c ∧
      (ntBeta n j hj) c < (ntBeta n j hj) a := by
  rintro ⟨a, b, c, hab, hbc, hbcv, hcav⟩
  have hac : a.val < c.val := lt_trans hab hbc
  obtain ⟨hb, hchi⟩ := ntBeta_force hj hbc hbcv
  rcases ntBeta_force_gt hj hac hcav with ha | hc
  · omega
  · omega

/-- A pattern in a swapped two-block permutation sits on the swap positions. -/
private lemma ntBeta_occur {n j : ℕ} (hj : j + 1 ≤ n) {P Q : Fin n} (hPQ : P ≠ Q)
    {κ : Equiv.Perm (Fin n)} (hκ : κ = ntBeta n j hj * Equiv.swap P Q)
    {i1 i2 i3 i4 : Fin n}
    (h12 : i1.val < i2.val) (h23 : i2.val < i3.val) (h34 : i3.val < i4.val)
    (hpat : ((κ i1 < κ i2 ∧ κ i2 < κ i3 ∧ κ i3 < κ i4) ∨
      (κ i3 < κ i4 ∧ κ i4 < κ i1 ∧ κ i1 < κ i2))) :
    (P = i1 ∧ Q = i3) ∨ (P = i3 ∧ Q = i1) ∨
    (P = i2 ∧ Q = i4) ∨ (P = i4 ∧ Q = i2) := by
  have d12 : i1 ≠ i2 := by intro h; subst h; exact lt_irrefl _ h12
  have d13 : i1 ≠ i3 := by
    intro h; subst h; exact lt_irrefl _ (lt_trans h12 h23)
  have d14 : i1 ≠ i4 := by
    intro h; subst h; exact lt_irrefl _ (lt_trans h12 (lt_trans h23 h34))
  have d23 : i2 ≠ i3 := by intro h; subst h; exact lt_irrefl _ h23
  have d24 : i2 ≠ i4 := by
    intro h; subst h; exact lt_irrefl _ (lt_trans h23 h34)
  have d34 : i3 ≠ i4 := by intro h; subst h; exact lt_irrefl _ h34
  have h13 : i1.val < i3.val := lt_trans h12 h23
  have h24 : i2.val < i4.val := lt_trans h23 h34
  have key : ∀ R S : Fin n, κ = ntBeta n j hj * Equiv.swap R S →
      (i1 = R ∨ i2 = R ∨ i3 = R ∨ i4 = R) := by
    intro R S hRS
    by_contra hcon
    simp only [not_or] at hcon
    obtain ⟨n1, n2, n3, n4⟩ := hcon
    have hag : ∀ w : Fin n, w ≠ R → w ≠ S → κ w = (ntBeta n j hj) w := by
      intro w hwR hwS
      rw [hRS, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hwR hwS]
    have a1 : i1 ≠ S → κ i1 = (ntBeta n j hj) i1 := fun h => hag i1 n1 h
    have a2 : i2 ≠ S → κ i2 = (ntBeta n j hj) i2 := fun h => hag i2 n2 h
    have a3 : i3 ≠ S → κ i3 = (ntBeta n j hj) i3 := fun h => hag i3 n3 h
    have a4 : i4 ≠ S → κ i4 = (ntBeta n j hj) i4 := fun h => hag i4 n4 h
    rcases hpat with h1234 | h3412
    · obtain ⟨g12, g23, g34⟩ := h1234
      rcases eq_or_ne S i1 with hS1|hS1
      · subst S
        have e2 := a2 (Ne.symm d12)
        have e3 := a3 (Ne.symm d13)
        have e4 := a4 (Ne.symm d14)
        rw [e2, e3] at g23
        rw [e3, e4] at g34
        exact ntBeta_no123 hj ⟨i2, i3, i4, h23, h34, g23, g34⟩
      · rcases eq_or_ne S i2 with hS2|hS2
        · subst S
          have e1 := a1 d12
          have e3 := a3 (Ne.symm d23)
          have e4 := a4 (Ne.symm d24)
          have h := lt_trans g12 g23
          rw [e1, e3] at h
          rw [e3, e4] at g34
          exact ntBeta_no123 hj ⟨i1, i3, i4, h13, h34, h, g34⟩
        · rcases eq_or_ne S i3 with hS3|hS3
          · subst S
            have e1 := a1 d13
            have e2 := a2 d23
            have e4 := a4 (Ne.symm d34)
            rw [e1, e2] at g12
            have h := lt_trans g23 g34
            rw [e2, e4] at h
            exact ntBeta_no123 hj ⟨i1, i2, i4, h12, h24, g12, h⟩
          · rcases eq_or_ne S i4 with hS4|hS4
            · subst S
              have e1 := a1 d14
              have e2 := a2 d24
              have e3 := a3 d34
              rw [e1, e2] at g12
              rw [e2, e3] at g23
              exact ntBeta_no123 hj ⟨i1, i2, i3, h12, h23, g12, g23⟩
            · have e1 := a1 (Ne.symm hS1)
              have e2 := a2 (Ne.symm hS2)
              have e3 := a3 (Ne.symm hS3)
              have e4 := a4 (Ne.symm hS4)
              rw [e1, e2] at g12
              rw [e2, e3] at g23
              exact ntBeta_no123 hj ⟨i1, i2, i3, h12, h23, g12, g23⟩
    · obtain ⟨g31, g42, g13⟩ := h3412
      rcases eq_or_ne S i1 with hS1|hS1
      · subst S
        have e2 := a2 (Ne.symm d12)
        have e3 := a3 (Ne.symm d13)
        have e4 := a4 (Ne.symm d14)
        rw [e3, e4] at g31
        have h := lt_trans g42 g13
        rw [e4, e2] at h
        exact ntBeta_no312 hj ⟨i2, i3, i4, h23, h34, g31, h⟩
      · rcases eq_or_ne S i2 with hS2|hS2
        · subst S
          have e1 := a1 d12
          have e3 := a3 (Ne.symm d23)
          have e4 := a4 (Ne.symm d24)
          rw [e3, e4] at g31
          rw [e4, e1] at g42
          exact ntBeta_no312 hj ⟨i1, i3, i4, h13, h34, g31, g42⟩
        · rcases eq_or_ne S i3 with hS3|hS3
          · subst S
            have e1 := a1 d13
            have e2 := a2 d23
            have e4 := a4 (Ne.symm d34)
            rw [e4, e1] at g42
            rw [e1, e2] at g13
            exact ntBeta_no231 hj ⟨i1, i2, i4, h12, h24, g42, g13⟩
          · rcases eq_or_ne S i4 with hS4|hS4
            · subst S
              have e1 := a1 d14
              have e2 := a2 d24
              have e3 := a3 d34
              have h := lt_trans g31 g42
              rw [e3, e1] at h
              rw [e1, e2] at g13
              exact ntBeta_no231 hj ⟨i1, i2, i3, h12, h23, h, g13⟩
            · have e1 := a1 (Ne.symm hS1)
              have e2 := a2 (Ne.symm hS2)
              have e3 := a3 (Ne.symm hS3)
              have e4 := a4 (Ne.symm hS4)
              have h := lt_trans g31 g42
              rw [e3, e1] at h
              rw [e1, e2] at g13
              exact ntBeta_no231 hj ⟨i1, i2, i3, h12, h23, h, g13⟩
  have hP4 := key P Q hκ
  have hκ' : κ = ntBeta n j hj * Equiv.swap Q P := by rw [hκ, Equiv.swap_comm]
  have hQ4 := key Q P hκ'
  rcases hP4 with rfl|rfl|rfl|rfl
  · rcases hQ4 with rfl|rfl|rfl|rfl
    · exact (hPQ rfl).elim
    · rcases hpat with h1234 | h3412
      · obtain ⟨g12, g23, g34⟩ := h1234
        have v1 : κ i1 = (ntBeta n j hj) i2 := by
          rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
        have v2 : κ i2 = (ntBeta n j hj) i1 := by
          rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_right]
        have v3 : κ i3 = (ntBeta n j hj) i3 := by
          rw [hκ, Equiv.Perm.mul_apply,
            Equiv.swap_apply_of_ne_of_ne (Ne.symm d13) (Ne.symm d23)]
        have v4 : κ i4 = (ntBeta n j hj) i4 := by
          rw [hκ, Equiv.Perm.mul_apply,
            Equiv.swap_apply_of_ne_of_ne (Ne.symm d14) (Ne.symm d24)]
        simp only [v1, v2, v3, v4] at g12 g23 g34
        exact False.elim (ntBeta_no123 hj ⟨i1, i3, i4, h13, h34, g23, g34⟩)
      · obtain ⟨g31, g42, g13⟩ := h3412
        have v1 : κ i1 = (ntBeta n j hj) i2 := by
          rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
        have v2 : κ i2 = (ntBeta n j hj) i1 := by
          rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_right]
        have v3 : κ i3 = (ntBeta n j hj) i3 := by
          rw [hκ, Equiv.Perm.mul_apply,
            Equiv.swap_apply_of_ne_of_ne (Ne.symm d13) (Ne.symm d23)]
        have v4 : κ i4 = (ntBeta n j hj) i4 := by
          rw [hκ, Equiv.Perm.mul_apply,
            Equiv.swap_apply_of_ne_of_ne (Ne.symm d14) (Ne.symm d24)]
        simp only [v1, v2, v3, v4] at g31 g42 g13
        have l41 : (ntBeta n j hj) i4 < (ntBeta n j hj) i1 := lt_trans g42 g13
        exact False.elim (ntBeta_no312 hj ⟨i1, i3, i4, h13, h34, g31, l41⟩)
    · exact Or.inl ⟨rfl, rfl⟩
    · rcases hpat with h1234 | h3412
      · obtain ⟨g12, g23, g34⟩ := h1234
        have v1 : κ i1 = (ntBeta n j hj) i4 := by
          rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
        have v2 : κ i2 = (ntBeta n j hj) i2 := by
          rw [hκ, Equiv.Perm.mul_apply,
            Equiv.swap_apply_of_ne_of_ne (Ne.symm d12) (d24)]
        have v3 : κ i3 = (ntBeta n j hj) i3 := by
          rw [hκ, Equiv.Perm.mul_apply,
            Equiv.swap_apply_of_ne_of_ne (Ne.symm d13) (d34)]
        have v4 : κ i4 = (ntBeta n j hj) i1 := by
          rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_right]
        simp only [v1, v2, v3, v4] at g12 g23 g34
        exact False.elim (ntBeta_no231 hj ⟨i2, i3, i4, h23, h34, g12, g23⟩)
      · obtain ⟨g31, g42, g13⟩ := h3412
        have v1 : κ i1 = (ntBeta n j hj) i4 := by
          rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
        have v2 : κ i2 = (ntBeta n j hj) i2 := by
          rw [hκ, Equiv.Perm.mul_apply,
            Equiv.swap_apply_of_ne_of_ne (Ne.symm d12) (d24)]
        have v3 : κ i3 = (ntBeta n j hj) i3 := by
          rw [hκ, Equiv.Perm.mul_apply,
            Equiv.swap_apply_of_ne_of_ne (Ne.symm d13) (d34)]
        have v4 : κ i4 = (ntBeta n j hj) i1 := by
          rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_right]
        simp only [v1, v2, v3, v4] at g31 g42 g13
        have l12 : (ntBeta n j hj) i1 < (ntBeta n j hj) i2 := lt_trans g42 g13
        exact False.elim (ntBeta_no231 hj ⟨i1, i2, i3, h12, h23, g31, l12⟩)
  · rcases hQ4 with rfl|rfl|rfl|rfl
    · rcases hpat with h1234 | h3412
      · obtain ⟨g12, g23, g34⟩ := h1234
        have v1 : κ i1 = (ntBeta n j hj) i2 := by
          rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_right]
        have v2 : κ i2 = (ntBeta n j hj) i1 := by
          rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
        have v3 : κ i3 = (ntBeta n j hj) i3 := by
          rw [hκ, Equiv.Perm.mul_apply,
            Equiv.swap_apply_of_ne_of_ne (Ne.symm d23) (Ne.symm d13)]
        have v4 : κ i4 = (ntBeta n j hj) i4 := by
          rw [hκ, Equiv.Perm.mul_apply,
            Equiv.swap_apply_of_ne_of_ne (Ne.symm d24) (Ne.symm d14)]
        simp only [v1, v2, v3, v4] at g12 g23 g34
        exact False.elim (ntBeta_no123 hj ⟨i1, i3, i4, h13, h34, g23, g34⟩)
      · obtain ⟨g31, g42, g13⟩ := h3412
        have v1 : κ i1 = (ntBeta n j hj) i2 := by
          rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_right]
        have v2 : κ i2 = (ntBeta n j hj) i1 := by
          rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
        have v3 : κ i3 = (ntBeta n j hj) i3 := by
          rw [hκ, Equiv.Perm.mul_apply,
            Equiv.swap_apply_of_ne_of_ne (Ne.symm d23) (Ne.symm d13)]
        have v4 : κ i4 = (ntBeta n j hj) i4 := by
          rw [hκ, Equiv.Perm.mul_apply,
            Equiv.swap_apply_of_ne_of_ne (Ne.symm d24) (Ne.symm d14)]
        simp only [v1, v2, v3, v4] at g31 g42 g13
        have l41 : (ntBeta n j hj) i4 < (ntBeta n j hj) i1 := lt_trans g42 g13
        exact False.elim (ntBeta_no312 hj ⟨i1, i3, i4, h13, h34, g31, l41⟩)
    · exact (hPQ rfl).elim
    · rcases hpat with h1234 | h3412
      · obtain ⟨g12, g23, g34⟩ := h1234
        have v1 : κ i1 = (ntBeta n j hj) i1 := by
          rw [hκ, Equiv.Perm.mul_apply,
            Equiv.swap_apply_of_ne_of_ne d12 d13]
        have v2 : κ i2 = (ntBeta n j hj) i3 := by
          rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
        have v3 : κ i3 = (ntBeta n j hj) i2 := by
          rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_right]
        have v4 : κ i4 = (ntBeta n j hj) i4 := by
          rw [hκ, Equiv.Perm.mul_apply,
            Equiv.swap_apply_of_ne_of_ne (Ne.symm d24) (Ne.symm d34)]
        simp only [v1, v2, v3, v4] at g12 g23 g34
        have l12 : (ntBeta n j hj) i1 < (ntBeta n j hj) i2 := lt_trans g12 g23
        exact False.elim (ntBeta_no123 hj ⟨i1, i2, i4, h12, h24, l12, g34⟩)
      · obtain ⟨g31, g42, g13⟩ := h3412
        have v1 : κ i1 = (ntBeta n j hj) i1 := by
          rw [hκ, Equiv.Perm.mul_apply,
            Equiv.swap_apply_of_ne_of_ne d12 d13]
        have v2 : κ i2 = (ntBeta n j hj) i3 := by
          rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
        have v3 : κ i3 = (ntBeta n j hj) i2 := by
          rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_right]
        have v4 : κ i4 = (ntBeta n j hj) i4 := by
          rw [hκ, Equiv.Perm.mul_apply,
            Equiv.swap_apply_of_ne_of_ne (Ne.symm d24) (Ne.symm d34)]
        simp only [v1, v2, v3, v4] at g31 g42 g13
        exact False.elim (ntBeta_no312 hj ⟨i1, i2, i4, h12, h24, g31, g42⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  · rcases hQ4 with rfl|rfl|rfl|rfl
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · rcases hpat with h1234 | h3412
      · obtain ⟨g12, g23, g34⟩ := h1234
        have v1 : κ i1 = (ntBeta n j hj) i1 := by
          rw [hκ, Equiv.Perm.mul_apply,
            Equiv.swap_apply_of_ne_of_ne d13 d12]
        have v2 : κ i2 = (ntBeta n j hj) i3 := by
          rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_right]
        have v3 : κ i3 = (ntBeta n j hj) i2 := by
          rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
        have v4 : κ i4 = (ntBeta n j hj) i4 := by
          rw [hκ, Equiv.Perm.mul_apply,
            Equiv.swap_apply_of_ne_of_ne (Ne.symm d34) (Ne.symm d24)]
        simp only [v1, v2, v3, v4] at g12 g23 g34
        have l12 : (ntBeta n j hj) i1 < (ntBeta n j hj) i2 := lt_trans g12 g23
        exact False.elim (ntBeta_no123 hj ⟨i1, i2, i4, h12, h24, l12, g34⟩)
      · obtain ⟨g31, g42, g13⟩ := h3412
        have v1 : κ i1 = (ntBeta n j hj) i1 := by
          rw [hκ, Equiv.Perm.mul_apply,
            Equiv.swap_apply_of_ne_of_ne d13 d12]
        have v2 : κ i2 = (ntBeta n j hj) i3 := by
          rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_right]
        have v3 : κ i3 = (ntBeta n j hj) i2 := by
          rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
        have v4 : κ i4 = (ntBeta n j hj) i4 := by
          rw [hκ, Equiv.Perm.mul_apply,
            Equiv.swap_apply_of_ne_of_ne (Ne.symm d34) (Ne.symm d24)]
        simp only [v1, v2, v3, v4] at g31 g42 g13
        exact False.elim (ntBeta_no312 hj ⟨i1, i2, i4, h12, h24, g31, g42⟩)
    · exact (hPQ rfl).elim
    · rcases hpat with h1234 | h3412
      · obtain ⟨g12, g23, g34⟩ := h1234
        have v1 : κ i1 = (ntBeta n j hj) i1 := by
          rw [hκ, Equiv.Perm.mul_apply,
            Equiv.swap_apply_of_ne_of_ne d13 d14]
        have v2 : κ i2 = (ntBeta n j hj) i2 := by
          rw [hκ, Equiv.Perm.mul_apply,
            Equiv.swap_apply_of_ne_of_ne d23 d24]
        have v3 : κ i3 = (ntBeta n j hj) i4 := by
          rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
        have v4 : κ i4 = (ntBeta n j hj) i3 := by
          rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_right]
        simp only [v1, v2, v3, v4] at g12 g23 g34
        have l23 : (ntBeta n j hj) i2 < (ntBeta n j hj) i3 := lt_trans g23 g34
        exact False.elim (ntBeta_no123 hj ⟨i1, i2, i3, h12, h23, g12, l23⟩)
      · obtain ⟨g31, g42, g13⟩ := h3412
        have v1 : κ i1 = (ntBeta n j hj) i1 := by
          rw [hκ, Equiv.Perm.mul_apply,
            Equiv.swap_apply_of_ne_of_ne d13 d14]
        have v2 : κ i2 = (ntBeta n j hj) i2 := by
          rw [hκ, Equiv.Perm.mul_apply,
            Equiv.swap_apply_of_ne_of_ne d23 d24]
        have v3 : κ i3 = (ntBeta n j hj) i4 := by
          rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
        have v4 : κ i4 = (ntBeta n j hj) i3 := by
          rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_right]
        simp only [v1, v2, v3, v4] at g31 g42 g13
        exact False.elim (ntBeta_no231 hj ⟨i1, i2, i3, h12, h23, g42, g13⟩)
  · rcases hQ4 with rfl|rfl|rfl|rfl
    · rcases hpat with h1234 | h3412
      · obtain ⟨g12, g23, g34⟩ := h1234
        have v1 : κ i1 = (ntBeta n j hj) i4 := by
          rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_right]
        have v2 : κ i2 = (ntBeta n j hj) i2 := by
          rw [hκ, Equiv.Perm.mul_apply,
            Equiv.swap_apply_of_ne_of_ne (d24) (Ne.symm d12)]
        have v3 : κ i3 = (ntBeta n j hj) i3 := by
          rw [hκ, Equiv.Perm.mul_apply,
            Equiv.swap_apply_of_ne_of_ne (d34) (Ne.symm d13)]
        have v4 : κ i4 = (ntBeta n j hj) i1 := by
          rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
        simp only [v1, v2, v3, v4] at g12 g23 g34
        exact False.elim (ntBeta_no231 hj ⟨i2, i3, i4, h23, h34, g12, g23⟩)
      · obtain ⟨g31, g42, g13⟩ := h3412
        have v1 : κ i1 = (ntBeta n j hj) i4 := by
          rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_right]
        have v2 : κ i2 = (ntBeta n j hj) i2 := by
          rw [hκ, Equiv.Perm.mul_apply,
            Equiv.swap_apply_of_ne_of_ne (d24) (Ne.symm d12)]
        have v3 : κ i3 = (ntBeta n j hj) i3 := by
          rw [hκ, Equiv.Perm.mul_apply,
            Equiv.swap_apply_of_ne_of_ne (d34) (Ne.symm d13)]
        have v4 : κ i4 = (ntBeta n j hj) i1 := by
          rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
        simp only [v1, v2, v3, v4] at g31 g42 g13
        have l12 : (ntBeta n j hj) i1 < (ntBeta n j hj) i2 := lt_trans g42 g13
        exact False.elim (ntBeta_no231 hj ⟨i1, i2, i3, h12, h23, g31, l12⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
    · rcases hpat with h1234 | h3412
      · obtain ⟨g12, g23, g34⟩ := h1234
        have v1 : κ i1 = (ntBeta n j hj) i1 := by
          rw [hκ, Equiv.Perm.mul_apply,
            Equiv.swap_apply_of_ne_of_ne d14 d13]
        have v2 : κ i2 = (ntBeta n j hj) i2 := by
          rw [hκ, Equiv.Perm.mul_apply,
            Equiv.swap_apply_of_ne_of_ne (d24) (d23)]
        have v3 : κ i3 = (ntBeta n j hj) i4 := by
          rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_right]
        have v4 : κ i4 = (ntBeta n j hj) i3 := by
          rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
        simp only [v1, v2, v3, v4] at g12 g23 g34
        have l23 : (ntBeta n j hj) i2 < (ntBeta n j hj) i3 := lt_trans g23 g34
        exact False.elim (ntBeta_no123 hj ⟨i1, i2, i3, h12, h23, g12, l23⟩)
      · obtain ⟨g31, g42, g13⟩ := h3412
        have v1 : κ i1 = (ntBeta n j hj) i1 := by
          rw [hκ, Equiv.Perm.mul_apply,
            Equiv.swap_apply_of_ne_of_ne d14 d13]
        have v2 : κ i2 = (ntBeta n j hj) i2 := by
          rw [hκ, Equiv.Perm.mul_apply,
            Equiv.swap_apply_of_ne_of_ne (d24) (d23)]
        have v3 : κ i3 = (ntBeta n j hj) i4 := by
          rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_right]
        have v4 : κ i4 = (ntBeta n j hj) i3 := by
          rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
        simp only [v1, v2, v3, v4] at g31 g42 g13
        exact False.elim (ntBeta_no231 hj ⟨i1, i2, i3, h12, h23, g42, g13⟩)
    · exact (hPQ rfl).elim

/-- Each `K` is closed under moves in both directions. -/
private lemma ntK_closed {n j : ℕ} (_hn : 5 ≤ n) (_hj1 : 1 ≤ j) (hjn : j + 1 ≤ n)
    {κ τ : Equiv.Perm (Fin n)}
    (hκ : κ ∈ ntK n j hjn) (h : ntMove n κ τ ∨ ntMove n τ κ) :
    τ ∈ ntK n j hjn := by
  obtain ⟨⟨P, Q, hPQ, hκT⟩, _hκP⟩ := hκ
  rcases h with hmove | hmove
  · obtain ⟨i1, i2, i3, i4, h12, h23, h34, s12, s23, s34, t1, t2, t3, t4,
      hrest⟩ := hmove
    have d12 : i1 ≠ i2 := by intro h; subst h; exact lt_irrefl _ h12
    have d14 : i1 ≠ i4 := by
      intro h; subst h; exact lt_irrefl _ (lt_trans h12 (lt_trans h23 h34))
    have d23 : i2 ≠ i3 := by intro h; subst h; exact lt_irrefl _ h23
    have d24 : i2 ≠ i4 := by
      intro h; subst h; exact lt_irrefl _ (lt_trans h23 h34)
    have d34 : i3 ≠ i4 := by intro h; subst h; exact lt_irrefl _ h34
    have d13 : i1 ≠ i3 := by
      intro h; subst h; exact absurd (lt_trans h12 h23) (lt_irrefl _)
    have heq : τ = κ * Equiv.swap i1 i3 * Equiv.swap i2 i4 :=
      ntMove_eq h12 h23 h34 s12 s23 s34 t1 t2 t3 t4 hrest
    have hpatκ : (κ i1 < κ i2 ∧ κ i2 < κ i3 ∧ κ i3 < κ i4) ∨
        (κ i3 < κ i4 ∧ κ i4 < κ i1 ∧ κ i1 < κ i2) :=
      Or.inl ⟨s12, s23, s34⟩
    have hocc := ntBeta_occur hjn hPQ hκT h12 h23 h34 hpatκ
    obtain ⟨c31, c42, c13⟩ :=
      ntMove_pat3412 h12 h23 h34 s12 s23 s34 t1 t2 t3 t4
    rcases hocc with ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩
    · subst P; subst Q
      have hτ : τ = ntBeta n j hjn * Equiv.swap i2 i4 := by
        have e : κ * Equiv.swap i1 i3 * Equiv.swap i2 i4 =
            ntBeta n j hjn * Equiv.swap i2 i4 := by
          rw [hκT, mul_assoc (ntBeta n j hjn) (Equiv.swap i1 i3)
            (Equiv.swap i1 i3), Equiv.swap_mul_self, mul_one]
        rw [heq]
        exact e
      refine ⟨⟨i2, i4, d24, hτ⟩,
        Or.inr ⟨i1, i2, i3, i4, h12, h23, h34, c31, c42, c13⟩⟩
    · subst P; subst Q
      have hκT' : κ = ntBeta n j hjn * Equiv.swap i1 i3 := by
        rw [hκT, Equiv.swap_comm]
      have hτ : τ = ntBeta n j hjn * Equiv.swap i2 i4 := by
        have e : κ * Equiv.swap i1 i3 * Equiv.swap i2 i4 =
            ntBeta n j hjn * Equiv.swap i2 i4 := by
          rw [hκT', mul_assoc (ntBeta n j hjn) (Equiv.swap i1 i3)
            (Equiv.swap i1 i3), Equiv.swap_mul_self, mul_one]
        rw [heq]
        exact e
      refine ⟨⟨i2, i4, d24, hτ⟩,
        Or.inr ⟨i1, i2, i3, i4, h12, h23, h34, c31, c42, c13⟩⟩
    · subst P; subst Q
      have hcomm : Equiv.swap i2 i4 * Equiv.swap i1 i3 =
          Equiv.swap i1 i3 * Equiv.swap i2 i4 :=
        ntSwap_comm_disjoint (Ne.symm d12) (d23) (Ne.symm d14)
          (Ne.symm d34)
      have hτ : τ = ntBeta n j hjn * Equiv.swap i1 i3 := by
        have e : κ * Equiv.swap i1 i3 * Equiv.swap i2 i4 =
            ntBeta n j hjn * Equiv.swap i1 i3 := by
          rw [hκT, mul_assoc (ntBeta n j hjn) (Equiv.swap i2 i4)
            (Equiv.swap i1 i3), hcomm,
            ← mul_assoc (ntBeta n j hjn) (Equiv.swap i1 i3)
            (Equiv.swap i2 i4),
            mul_assoc (ntBeta n j hjn * Equiv.swap i1 i3)
            (Equiv.swap i2 i4) (Equiv.swap i2 i4),
            Equiv.swap_mul_self, mul_one]
        rw [heq]
        exact e
      refine ⟨⟨i1, i3, d13, hτ⟩,
        Or.inr ⟨i1, i2, i3, i4, h12, h23, h34, c31, c42, c13⟩⟩
    · subst P; subst Q
      have hκT' : κ = ntBeta n j hjn * Equiv.swap i2 i4 := by
        rw [hκT, Equiv.swap_comm]
      have hcomm : Equiv.swap i2 i4 * Equiv.swap i1 i3 =
          Equiv.swap i1 i3 * Equiv.swap i2 i4 :=
        ntSwap_comm_disjoint (Ne.symm d12) (d23) (Ne.symm d14)
          (Ne.symm d34)
      have hτ : τ = ntBeta n j hjn * Equiv.swap i1 i3 := by
        have e : κ * Equiv.swap i1 i3 * Equiv.swap i2 i4 =
            ntBeta n j hjn * Equiv.swap i1 i3 := by
          rw [hκT', mul_assoc (ntBeta n j hjn) (Equiv.swap i2 i4)
            (Equiv.swap i1 i3), hcomm,
            ← mul_assoc (ntBeta n j hjn) (Equiv.swap i1 i3)
            (Equiv.swap i2 i4),
            mul_assoc (ntBeta n j hjn * Equiv.swap i1 i3)
            (Equiv.swap i2 i4) (Equiv.swap i2 i4),
            Equiv.swap_mul_self, mul_one]
        rw [heq]
        exact e
      refine ⟨⟨i1, i3, d13, hτ⟩,
        Or.inr ⟨i1, i2, i3, i4, h12, h23, h34, c31, c42, c13⟩⟩
  · obtain ⟨i1, i2, i3, i4, h12, h23, h34, s12, s23, s34, t1, t2, t3, t4,
      hrest⟩ := hmove
    have d12 : i1 ≠ i2 := by intro h; subst h; exact lt_irrefl _ h12
    have d14 : i1 ≠ i4 := by
      intro h; subst h; exact lt_irrefl _ (lt_trans h12 (lt_trans h23 h34))
    have d23 : i2 ≠ i3 := by intro h; subst h; exact lt_irrefl _ h23
    have d24 : i2 ≠ i4 := by
      intro h; subst h; exact lt_irrefl _ (lt_trans h23 h34)
    have d34 : i3 ≠ i4 := by intro h; subst h; exact lt_irrefl _ h34
    have d13 : i1 ≠ i3 := by
      intro h; subst h; exact absurd (lt_trans h12 h23) (lt_irrefl _)
    have heq : κ = τ * Equiv.swap i1 i3 * Equiv.swap i2 i4 :=
      ntMove_eq h12 h23 h34 s12 s23 s34 t1 t2 t3 t4 hrest
    obtain ⟨c31, c42, c13⟩ :=
      ntMove_pat3412 h12 h23 h34 s12 s23 s34 t1 t2 t3 t4
    have hpatκ : (κ i1 < κ i2 ∧ κ i2 < κ i3 ∧ κ i3 < κ i4) ∨
        (κ i3 < κ i4 ∧ κ i4 < κ i1 ∧ κ i1 < κ i2) :=
      Or.inr ⟨c31, c42, c13⟩
    have hocc := ntBeta_occur hjn hPQ hκT h12 h23 h34 hpatκ
    have sq13 : Equiv.swap i1 i3 * Equiv.swap i1 i3 = 1 :=
      Equiv.swap_mul_self _ _
    have sq24 : Equiv.swap i2 i4 * Equiv.swap i2 i4 = 1 :=
      Equiv.swap_mul_self _ _
    have hcomm : Equiv.swap i1 i3 * Equiv.swap i2 i4 =
        Equiv.swap i2 i4 * Equiv.swap i1 i3 :=
      ntSwap_comm_disjoint d12 d14 (Ne.symm d23) d34
    rcases hocc with ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩
    · subst P; subst Q
      have h1 : τ * Equiv.swap i1 i3 * Equiv.swap i2 i4 =
          ntBeta n j hjn * Equiv.swap i1 i3 := by rw [← heq, hκT]
      have hstep : τ * Equiv.swap i2 i4 = ntBeta n j hjn :=
        ntSwap_cancel_mid sq13 hcomm h1
      have hτ : τ = ntBeta n j hjn * Equiv.swap i2 i4 := by
        rw [← hstep, mul_assoc τ (Equiv.swap i2 i4) (Equiv.swap i2 i4), sq24,
          mul_one]
      refine ⟨⟨i2, i4, d24, hτ⟩,
        Or.inl ⟨i1, i2, i3, i4, h12, h23, h34, s12, s23, s34⟩⟩
    · subst P; subst Q
      have hκT' : κ = ntBeta n j hjn * Equiv.swap i1 i3 := by
        rw [hκT, Equiv.swap_comm]
      have h1 : τ * Equiv.swap i1 i3 * Equiv.swap i2 i4 =
          ntBeta n j hjn * Equiv.swap i1 i3 := by rw [← heq, hκT']
      have hstep : τ * Equiv.swap i2 i4 = ntBeta n j hjn :=
        ntSwap_cancel_mid sq13 hcomm h1
      have hτ : τ = ntBeta n j hjn * Equiv.swap i2 i4 := by
        rw [← hstep, mul_assoc τ (Equiv.swap i2 i4) (Equiv.swap i2 i4), sq24,
          mul_one]
      refine ⟨⟨i2, i4, d24, hτ⟩,
        Or.inl ⟨i1, i2, i3, i4, h12, h23, h34, s12, s23, s34⟩⟩
    · subst P; subst Q
      have h1 : τ * Equiv.swap i1 i3 * Equiv.swap i2 i4 =
          ntBeta n j hjn * Equiv.swap i2 i4 := by rw [← heq, hκT]
      have hstep : τ * Equiv.swap i1 i3 = ntBeta n j hjn :=
        ntSwap_cancel_end sq24 h1
      have hτ : τ = ntBeta n j hjn * Equiv.swap i1 i3 := by
        rw [← hstep, mul_assoc τ (Equiv.swap i1 i3) (Equiv.swap i1 i3), sq13,
          mul_one]
      refine ⟨⟨i1, i3, d13, hτ⟩,
        Or.inl ⟨i1, i2, i3, i4, h12, h23, h34, s12, s23, s34⟩⟩
    · subst P; subst Q
      have hκT' : κ = ntBeta n j hjn * Equiv.swap i2 i4 := by
        rw [hκT, Equiv.swap_comm]
      have h1 : τ * Equiv.swap i1 i3 * Equiv.swap i2 i4 =
          ntBeta n j hjn * Equiv.swap i2 i4 := by rw [← heq, hκT']
      have hstep : τ * Equiv.swap i1 i3 = ntBeta n j hjn :=
        ntSwap_cancel_end sq24 h1
      have hτ : τ = ntBeta n j hjn * Equiv.swap i1 i3 := by
        rw [← hstep, mul_assoc τ (Equiv.swap i1 i3) (Equiv.swap i1 i3), sq13,
          mul_one]
      refine ⟨⟨i1, i3, d13, hτ⟩,
        Or.inl ⟨i1, i2, i3, i4, h12, h23, h34, s12, s23, s34⟩⟩

/-- Swapping adjacent positions of the two-block permutation yields no pattern. -/
private lemma ntK_noPat_adjacent {n j : ℕ} (hj : j + 1 ≤ n) {P Q : Fin n}
    (hPQ : P ≠ Q) (hadj : Q.val = P.val + 1 ∨ P.val = Q.val + 1)
    {κ : Equiv.Perm (Fin n)} (hκ : κ = ntBeta n j hj * Equiv.swap P Q) :
    ¬ ntPat n κ := by
  intro hpat
  rcases hpat with ⟨i1, i2, i3, i4, h12, h23, h34, g12, g23, g34⟩ |
    ⟨i1, i2, i3, i4, h12, h23, h34, g31, g42, g13⟩
  · have hocc := ntBeta_occur hj hPQ hκ h12 h23 h34 (Or.inl ⟨g12, g23, g34⟩)
    rcases hocc with ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩ <;>
      rw [hP, hQ] at hadj <;> omega
  · have hocc := ntBeta_occur hj hPQ hκ h12 h23 h34 (Or.inr ⟨g31, g42, g13⟩)
    rcases hocc with ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩ <;>
      rw [hP, hQ] at hadj <;> omega

/-- The high hub `beta * swap j (n-1)` has a 1234 pattern. -/
private lemma ntK_highHub_pat {n j : ℕ} (hn : 5 ≤ n) (hj1 : 1 ≤ j)
    (hjn : j + 1 ≤ n) (hj3 : j + 3 ≤ n)
    {J N1 : Fin n} (hJ : J.val = j) (hN1 : N1.val = n - 1) :
    ntPat n (ntBeta n j hjn * Equiv.swap J N1) := by
  have h0lt : 0 < n := by omega
  have hJ1lt : j + 1 < n := by omega
  have hZv : ((⟨0, h0lt⟩ : Fin n)).val = 0 := rfl
  have hJ1v : ((⟨j + 1, hJ1lt⟩ : Fin n)).val = j + 1 := rfl
  have dZJ : (⟨0, h0lt⟩ : Fin n) ≠ J := Fin.ne_of_val_ne (by omega)
  have dZN : (⟨0, h0lt⟩ : Fin n) ≠ N1 := Fin.ne_of_val_ne (by omega)
  have dJ1J : (⟨j + 1, hJ1lt⟩ : Fin n) ≠ J := Fin.ne_of_val_ne (by omega)
  have dJ1N : (⟨j + 1, hJ1lt⟩ : Fin n) ≠ N1 := Fin.ne_of_val_ne (by omega)
  have eJ : (ntBeta n j hjn * Equiv.swap J N1) J = ntBeta n j hjn N1 := by
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
  have eN : (ntBeta n j hjn * Equiv.swap J N1) N1 = ntBeta n j hjn J := by
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right]
  have v0 : ((ntBeta n j hjn * Equiv.swap J N1) (⟨0, h0lt⟩ : Fin n)).val =
      j - 1 := by
    rw [ntHub_val hjn _ dZJ dZN, ntBeta_val]
    rw [ite_eq_left (by omega : (⟨0, h0lt⟩ : Fin n).val < j)]
    simp only [Nat.sub_zero]
  have vJ : ((ntBeta n j hjn * Equiv.swap J N1) J).val = j := by
    have e : ((ntBeta n j hjn * Equiv.swap J N1) J).val =
        ((ntBeta n j hjn) N1).val := congrArg Fin.val eJ
    rw [e, ntBeta_val]
    rw [ite_eq_right (by omega : ¬ N1.val < j)]
    rw [hN1]
    have hnn := N1.is_lt
    omega
  have vJ1 : ((ntBeta n j hjn * Equiv.swap J N1) ⟨j + 1, hJ1lt⟩).val = n - 2 := by
    rw [ntHub_val hjn _ dJ1J dJ1N, ntBeta_val]
    rw [ite_eq_right (by omega : ¬ (⟨j + 1, hJ1lt⟩ : Fin n).val < j)]
    rw [hJ1v]
    have hnn : j + 1 < n := hJ1lt
    omega
  have vN : ((ntBeta n j hjn * Equiv.swap J N1) N1).val = n - 1 := by
    have e : ((ntBeta n j hjn * Equiv.swap J N1) N1).val =
        ((ntBeta n j hjn) J).val := congrArg Fin.val eN
    rw [e, ntBeta_val]
    rw [ite_eq_right (by omega : ¬ J.val < j)]
    rw [hJ]
    have hnn := N1.is_lt
    omega
  refine Or.inl ⟨(⟨0, h0lt⟩ : Fin n), J, ⟨j + 1, hJ1lt⟩, N1, by omega, by omega,
    by omega, by rw [Fin.lt_def]; omega, by rw [Fin.lt_def]; omega,
    by rw [Fin.lt_def]; omega⟩

/-- The low hub `beta * swap 0 (j-1)` has a 1234 pattern. -/
private lemma ntK_lowHub_pat {n j : ℕ} (hn : 5 ≤ n)
    (hjn : j + 1 ≤ n) (hj3 : 3 ≤ j)
    {Z J1 : Fin n} (hZ : Z.val = 0) (hJ1 : J1.val = j - 1) :
    ntPat n (ntBeta n j hjn * Equiv.swap Z J1) := by
  have hOlt : 1 < n := by omega
  have hN1lt : n - 1 < n := by omega
  have hOv : ((⟨1, hOlt⟩ : Fin n)).val = 1 := rfl
  have hN1v : ((⟨n - 1, hN1lt⟩ : Fin n)).val = n - 1 := rfl
  have dOZ : (⟨1, hOlt⟩ : Fin n) ≠ Z := Fin.ne_of_val_ne (by omega)
  have dOJ : (⟨1, hOlt⟩ : Fin n) ≠ J1 := Fin.ne_of_val_ne (by omega)
  have dNZ : (⟨n - 1, hN1lt⟩ : Fin n) ≠ Z := Fin.ne_of_val_ne (by omega)
  have dNJ : (⟨n - 1, hN1lt⟩ : Fin n) ≠ J1 := Fin.ne_of_val_ne (by omega)
  have eZ : (ntBeta n j hjn * Equiv.swap Z J1) Z = ntBeta n j hjn J1 := by
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
  have eJ : (ntBeta n j hjn * Equiv.swap Z J1) J1 = ntBeta n j hjn Z := by
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right]
  have vZ : ((ntBeta n j hjn * Equiv.swap Z J1) Z).val = 0 := by
    have e : ((ntBeta n j hjn * Equiv.swap Z J1) Z).val =
        ((ntBeta n j hjn) J1).val := congrArg Fin.val eZ
    rw [e, ntBeta_val]
    rw [ite_eq_left (by omega : J1.val < j)]
    rw [hJ1]
    omega
  have vO : ((ntBeta n j hjn * Equiv.swap Z J1) ⟨1, hOlt⟩).val = j - 2 := by
    rw [ntHub_val hjn _ dOZ dOJ, ntBeta_val]
    rw [ite_eq_left (by omega : (⟨1, hOlt⟩ : Fin n).val < j)]
    rw [hOv]
    omega
  have vJ : ((ntBeta n j hjn * Equiv.swap Z J1) J1).val = j - 1 := by
    have e : ((ntBeta n j hjn * Equiv.swap Z J1) J1).val =
        ((ntBeta n j hjn) Z).val := congrArg Fin.val eJ
    rw [e, ntBeta_val]
    rw [ite_eq_left (by omega : Z.val < j)]
    rw [hZ]
    simp only [Nat.sub_zero]
  have vN : ((ntBeta n j hjn * Equiv.swap Z J1) ⟨n - 1, hN1lt⟩).val = j := by
    rw [ntHub_val hjn _ dNZ dNJ, ntBeta_val]
    rw [ite_eq_right (by omega : ¬ (⟨n - 1, hN1lt⟩ : Fin n).val < j)]
    rw [hN1v]
    have hnn : n - 1 < n := hN1lt
    omega
  refine Or.inl ⟨Z, ⟨1, hOlt⟩, J1, ⟨n - 1, hN1lt⟩, by omega, by omega,
    by omega, by rw [Fin.lt_def]; omega, by rw [Fin.lt_def]; omega,
    by rw [Fin.lt_def]; omega⟩

/-- A low non-adjacent pair moves to a mixed pair. -/
private lemma ntK_lowMove {n j : ℕ} (hjn : j + 1 ≤ n)
    {P Q : Fin n} (hPlow : P.val < j) (hQlow : Q.val < j)
    (hPQ2 : P.val + 2 ≤ Q.val)
    {P1 J : Fin n} (hP1 : P1.val = P.val + 1) (hJ : J.val = j)
    {κ : Equiv.Perm (Fin n)} (hκ : κ = ntBeta n j hjn * Equiv.swap P Q) :
    Relation.EqvGen (ntMove n) κ (ntBeta n j hjn * Equiv.swap P1 J) := by
  have dP1P : P1 ≠ P := Fin.ne_of_val_ne (by omega)
  have dPJ : P ≠ J := Fin.ne_of_val_ne (by omega)
  have dP1Q : P1 ≠ Q := Fin.ne_of_val_ne (by omega)
  have dP1J : P1 ≠ J := Fin.ne_of_val_ne (by omega)
  have dQJ : Q ≠ J := Fin.ne_of_val_ne (by omega)
  have h12 : P.val < P1.val := by omega
  have h23 : P1.val < Q.val := by omega
  have h34 : Q.val < J.val := by omega
  have vP : (κ P).val = j - 1 - Q.val := by
    have eP : κ P = ntBeta n j hjn Q := by
      rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    rw [eP, ntBeta_val, ite_eq_left hQlow]
  have vP1 : (κ P1).val = j - 1 - P1.val := by
    have eP1 : κ P1 = ntBeta n j hjn P1 := by
      rw [hκ, Equiv.Perm.mul_apply,
        Equiv.swap_apply_of_ne_of_ne dP1P dP1Q]
    rw [eP1, ntBeta_val, ite_eq_left (by omega : P1.val < j)]
  have vQ : (κ Q).val = j - 1 - P.val := by
    have eQ : κ Q = ntBeta n j hjn P := by
      rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_right]
    rw [eQ, ntBeta_val, ite_eq_left hPlow]
  have vJ : (κ J).val = n - 1 := by
    have eJ : κ J = ntBeta n j hjn J := by
      rw [hκ, Equiv.Perm.mul_apply,
        Equiv.swap_apply_of_ne_of_ne dPJ.symm dQJ.symm]
    rw [eJ, ntBeta_val, ite_eq_right (by omega : ¬ J.val < j), hJ]
    have hle : j + 1 ≤ n := hjn
    omega
  have s12 : κ P < κ P1 := by rw [Fin.lt_def]; omega
  have s23 : κ P1 < κ Q := by rw [Fin.lt_def]; omega
  have s34 : κ Q < κ J := by rw [Fin.lt_def]; omega
  have hmove : ntMove n κ (κ * Equiv.swap P Q * Equiv.swap P1 J) :=
    ntMove_of_1234 h12 h23 h34 s12 s23 s34
  have hres : κ * Equiv.swap P Q * Equiv.swap P1 J =
      ntBeta n j hjn * Equiv.swap P1 J := by
    rw [hκ, mul_assoc (ntBeta n j hjn) (Equiv.swap P Q) (Equiv.swap P Q),
      Equiv.swap_mul_self, mul_one]
  rw [hres] at hmove
  exact Relation.EqvGen.rel _ _ hmove

/-- A high non-adjacent pair moves to a mixed pair. -/
private lemma ntK_highMove {n j : ℕ} (hj1 : 1 ≤ j) (hjn : j + 1 ≤ n)
    {P Q : Fin n} (hPhigh : j ≤ P.val) (hQhigh : j ≤ Q.val)
    (hPQ2 : P.val + 2 ≤ Q.val)
    {J1 P1 : Fin n} (hJ1 : J1.val = j - 1) (hP1 : P1.val = P.val + 1)
    {κ : Equiv.Perm (Fin n)} (hκ : κ = ntBeta n j hjn * Equiv.swap P Q) :
    Relation.EqvGen (ntMove n) κ (ntBeta n j hjn * Equiv.swap J1 P1) := by
  have dJ1P : J1 ≠ P := Fin.ne_of_val_ne (by omega)
  have dJ1Q : J1 ≠ Q := Fin.ne_of_val_ne (by omega)
  have dP1P : P1 ≠ P := Fin.ne_of_val_ne (by omega)
  have dP1Q : P1 ≠ Q := Fin.ne_of_val_ne (by omega)
  have h12 : J1.val < P.val := by omega
  have h23 : P.val < P1.val := by omega
  have h34 : P1.val < Q.val := by omega
  have vJ1 : (κ J1).val = 0 := by
    have eJ1 : κ J1 = ntBeta n j hjn J1 := by
      rw [hκ, Equiv.Perm.mul_apply,
        Equiv.swap_apply_of_ne_of_ne dJ1P dJ1Q]
    rw [eJ1, ntBeta_val, ite_eq_left (by omega : J1.val < j), hJ1]
    omega
  have vP : (κ P).val = n + j - 1 - Q.val := by
    have eP : κ P = ntBeta n j hjn Q := by
      rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    have e : (κ P).val = ((ntBeta n j hjn) Q).val := congrArg Fin.val eP
    rw [e, ntBeta_val, ite_eq_right (by omega : ¬ Q.val < j)]
  have vP1 : (κ P1).val = n + j - 1 - P1.val := by
    have eP1 : κ P1 = ntBeta n j hjn P1 := by
      rw [hκ, Equiv.Perm.mul_apply,
        Equiv.swap_apply_of_ne_of_ne dP1P dP1Q]
    rw [eP1, ntBeta_val, ite_eq_right (by omega : ¬ P1.val < j)]
  have vQ : (κ Q).val = n + j - 1 - P.val := by
    have eQ : κ Q = ntBeta n j hjn P := by
      rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_right]
    have e : (κ Q).val = ((ntBeta n j hjn) P).val := congrArg Fin.val eQ
    rw [e, ntBeta_val, ite_eq_right (by omega : ¬ P.val < j)]
  have s12 : κ J1 < κ P := by rw [Fin.lt_def]; omega
  have s23 : κ P < κ P1 := by rw [Fin.lt_def]; omega
  have s34 : κ P1 < κ Q := by rw [Fin.lt_def]; omega
  have hmove : ntMove n κ (κ * Equiv.swap J1 P1 * Equiv.swap P Q) :=
    ntMove_of_1234 h12 h23 h34 s12 s23 s34
  have hcomm : Equiv.swap P Q * Equiv.swap J1 P1 =
      Equiv.swap J1 P1 * Equiv.swap P Q :=
    ntSwap_comm_disjoint dJ1P.symm dP1P.symm dJ1Q.symm dP1Q.symm
  have hres : κ * Equiv.swap J1 P1 * Equiv.swap P Q =
      ntBeta n j hjn * Equiv.swap J1 P1 := by
    rw [hκ, mul_assoc (ntBeta n j hjn) (Equiv.swap P Q) (Equiv.swap J1 P1),
      hcomm, ← mul_assoc (ntBeta n j hjn) (Equiv.swap J1 P1)
      (Equiv.swap P Q),
      mul_assoc (ntBeta n j hjn * Equiv.swap J1 P1)
      (Equiv.swap P Q) (Equiv.swap P Q),
      Equiv.swap_mul_self, mul_one]
  rw [hres] at hmove
  exact Relation.EqvGen.rel _ _ hmove

/-- The low hub moves to any interior mixed pair. -/
private lemma ntK_lowHubMove {n j : ℕ} (hj1 : 1 ≤ j) (hjn : j + 1 ≤ n)
    {Z J1 : Fin n} (hZ : Z.val = 0) (hJ1 : J1.val = j - 1)
    {U W : Fin n} (hU0 : 0 < U.val) (hUJ : U.val < j - 1) (hWJ : j ≤ W.val)
    {κ : Equiv.Perm (Fin n)} (hκ : κ = ntBeta n j hjn * Equiv.swap Z J1) :
    Relation.EqvGen (ntMove n) κ (ntBeta n j hjn * Equiv.swap U W) := by
  have hWlt := W.is_lt
  have dUZ : U ≠ Z := Fin.ne_of_val_ne (by omega)
  have dUJ : U ≠ J1 := Fin.ne_of_val_ne (by omega)
  have dWZ : W ≠ Z := Fin.ne_of_val_ne (by omega)
  have dWJ1 : W ≠ J1 := Fin.ne_of_val_ne (by omega)
  have h12 : Z.val < U.val := by omega
  have h23 : U.val < J1.val := by omega
  have h34 : J1.val < W.val := by omega
  have vZ : (κ Z).val = 0 := by
    have eZ : κ Z = ntBeta n j hjn J1 := by
      rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    have e : (κ Z).val = ((ntBeta n j hjn) J1).val := congrArg Fin.val eZ
    rw [e, ntBeta_val, ite_eq_left (by omega : J1.val < j), hJ1]
    omega
  have vU : (κ U).val = j - 1 - U.val := by
    have eU : κ U = ntBeta n j hjn U := by
      rw [hκ, Equiv.Perm.mul_apply,
        Equiv.swap_apply_of_ne_of_ne dUZ dUJ]
    rw [eU, ntBeta_val, ite_eq_left (by omega : U.val < j)]
  have vJ : (κ J1).val = j - 1 := by
    have eJ : κ J1 = ntBeta n j hjn Z := by
      rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_right]
    have e : (κ J1).val = ((ntBeta n j hjn) Z).val := congrArg Fin.val eJ
    rw [e, ntBeta_val, ite_eq_left (by omega : Z.val < j), hZ]
    simp only [Nat.sub_zero]
  have vW : (κ W).val = n + j - 1 - W.val := by
    have eW : κ W = ntBeta n j hjn W := by
      rw [hκ, Equiv.Perm.mul_apply,
        Equiv.swap_apply_of_ne_of_ne dWZ dWJ1]
    rw [eW, ntBeta_val, ite_eq_right (by omega : ¬ W.val < j)]
  have s12 : κ Z < κ U := by rw [Fin.lt_def]; omega
  have s23 : κ U < κ J1 := by rw [Fin.lt_def]; omega
  have s34 : κ J1 < κ W := by rw [Fin.lt_def]; omega
  have hmove : ntMove n κ (κ * Equiv.swap Z J1 * Equiv.swap U W) :=
    ntMove_of_1234 h12 h23 h34 s12 s23 s34
  have hres : κ * Equiv.swap Z J1 * Equiv.swap U W =
      ntBeta n j hjn * Equiv.swap U W := by
    rw [hκ, mul_assoc (ntBeta n j hjn) (Equiv.swap Z J1) (Equiv.swap Z J1),
      Equiv.swap_mul_self, mul_one]
  rw [hres] at hmove
  exact Relation.EqvGen.rel _ _ hmove

/-- The high hub moves to any interior mixed pair. -/
private lemma ntK_highHubMove {n j : ℕ} (hj1 : 1 ≤ j) (hjn : j + 1 ≤ n)
    {J N1 : Fin n} (hJ : J.val = j) (hN1 : N1.val = n - 1)
    {U W : Fin n} (hUJ : U.val < j) (hJW : j < W.val) (hWN : W.val < n - 1)
    {κ : Equiv.Perm (Fin n)} (hκ : κ = ntBeta n j hjn * Equiv.swap J N1) :
    Relation.EqvGen (ntMove n) κ (ntBeta n j hjn * Equiv.swap U W) := by
  have dUJ : U ≠ J := Fin.ne_of_val_ne (by omega)
  have dUN : U ≠ N1 := Fin.ne_of_val_ne (by omega)
  have dWJ : W ≠ J := Fin.ne_of_val_ne (by omega)
  have dWN : W ≠ N1 := Fin.ne_of_val_ne (by omega)
  have h12 : U.val < J.val := by omega
  have h23 : J.val < W.val := by omega
  have h34 : W.val < N1.val := by omega
  have vU : (κ U).val = j - 1 - U.val := by
    have eU : κ U = ntBeta n j hjn U := by
      rw [hκ, Equiv.Perm.mul_apply,
        Equiv.swap_apply_of_ne_of_ne dUJ dUN]
    rw [eU, ntBeta_val, ite_eq_left hUJ]
  have vJ : (κ J).val = j := by
    have eJ : κ J = ntBeta n j hjn N1 := by
      rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    have e : (κ J).val = ((ntBeta n j hjn) N1).val := congrArg Fin.val eJ
    rw [e, ntBeta_val, ite_eq_right (by omega : ¬ N1.val < j), hN1]
    have hnn := N1.is_lt
    omega
  have vW : (κ W).val = n + j - 1 - W.val := by
    have eW : κ W = ntBeta n j hjn W := by
      rw [hκ, Equiv.Perm.mul_apply,
        Equiv.swap_apply_of_ne_of_ne dWJ dWN]
    rw [eW, ntBeta_val, ite_eq_right (by omega : ¬ W.val < j)]
  have vN : (κ N1).val = n - 1 := by
    have eN : κ N1 = ntBeta n j hjn J := by
      rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_right]
    have e : (κ N1).val = ((ntBeta n j hjn) J).val := congrArg Fin.val eN
    rw [e, ntBeta_val, ite_eq_right (by omega : ¬ J.val < j), hJ]
    have hnn := N1.is_lt
    omega
  have s12 : κ U < κ J := by rw [Fin.lt_def]; omega
  have s23 : κ J < κ W := by rw [Fin.lt_def]; omega
  have s34 : κ W < κ N1 := by rw [Fin.lt_def]; omega
  have hmove : ntMove n κ (κ * Equiv.swap U W * Equiv.swap J N1) :=
    ntMove_of_1234 h12 h23 h34 s12 s23 s34
  have hcomm : Equiv.swap J N1 * Equiv.swap U W =
      Equiv.swap U W * Equiv.swap J N1 :=
    ntSwap_comm_disjoint dUJ.symm dWJ.symm dUN.symm dWN.symm
  have hres : κ * Equiv.swap U W * Equiv.swap J N1 =
      ntBeta n j hjn * Equiv.swap U W := by
    rw [hκ, mul_assoc (ntBeta n j hjn) (Equiv.swap J N1) (Equiv.swap U W),
      hcomm, ← mul_assoc (ntBeta n j hjn) (Equiv.swap U W)
      (Equiv.swap J N1),
      mul_assoc (ntBeta n j hjn * Equiv.swap U W)
      (Equiv.swap J N1) (Equiv.swap J N1),
      Equiv.swap_mul_self, mul_one]
  rw [hres] at hmove
  exact Relation.EqvGen.rel _ _ hmove

/-- The extreme pair `(0, j)` has no pattern: `kappa` takes the maximum there. -/
private lemma ntK_noPat_C1 {n j : ℕ} (hj : j + 1 ≤ n)
    {P Q : Fin n} (hPQ : P ≠ Q) (hP0 : P.val = 0) (hQj : Q.val = j)
    {κ : Equiv.Perm (Fin n)} (hκ : κ = ntBeta n j hj * Equiv.swap P Q) :
    ¬ ntPat n κ := by
  have vP : (κ P).val = n - 1 := by
    have eP : κ P = ntBeta n j hj Q := by
      rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    have e : (κ P).val = ((ntBeta n j hj) Q).val := congrArg Fin.val eP
    rw [e, ntBeta_val, ite_eq_right (by omega : ¬ Q.val < j), hQj]
    have hle : j + 1 ≤ n := hj
    omega
  intro hpat
  rcases hpat with ⟨i1, i2, i3, i4, h12, h23, h34, g12, g23, g34⟩ |
    ⟨i1, i2, i3, i4, h12, h23, h34, g31, g42, g13⟩
  · have hocc := ntBeta_occur hj hPQ hκ h12 h23 h34 (Or.inl ⟨g12, g23, g34⟩)
    have hi2 := (κ i2).is_lt
    rcases hocc with ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩
    · rw [← hP] at g12
      rw [Fin.lt_def, vP] at g12
      omega
    · have h3 : i3.val = 0 := by rw [← hP]; exact hP0
      omega
    · have h2 : i2.val = 0 := by rw [← hP]; exact hP0
      omega
    · have h4 : i4.val = 0 := by rw [← hP]; exact hP0
      omega
  · have hocc := ntBeta_occur hj hPQ hκ h12 h23 h34 (Or.inr ⟨g31, g42, g13⟩)
    have hi2 := (κ i2).is_lt
    rcases hocc with ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩
    · rw [← hP] at g13
      rw [Fin.lt_def, vP] at g13
      omega
    · have h3 : i3.val = 0 := by rw [← hP]; exact hP0
      omega
    · have h2 : i2.val = 0 := by rw [← hP]; exact hP0
      omega
    · have h4 : i4.val = 0 := by rw [← hP]; exact hP0
      omega

/-- The extreme pair `(0, n-1)` has no pattern. -/
private lemma ntK_noPat_C2 {n j : ℕ} (hj1 : 1 ≤ j) (hj : j + 1 ≤ n)
    {P Q : Fin n} (hPQ : P ≠ Q) (hP0 : P.val = 0) (hQn : Q.val = n - 1)
    {κ : Equiv.Perm (Fin n)} (hκ : κ = ntBeta n j hj * Equiv.swap P Q) :
    ¬ ntPat n κ := by
  have vP : (κ P).val = j := by
    have eP : κ P = ntBeta n j hj Q := by
      rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    have e : (κ P).val = ((ntBeta n j hj) Q).val := congrArg Fin.val eP
    rw [e, ntBeta_val, ite_eq_right (by omega : ¬ Q.val < j), hQn]
    have hle : j + 1 ≤ n := hj
    have hnn := Q.is_lt
    omega
  have vQ : (κ Q).val = j - 1 := by
    have eQ : κ Q = ntBeta n j hj P := by
      rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_right]
    have e : (κ Q).val = ((ntBeta n j hj) P).val := congrArg Fin.val eQ
    rw [e, ntBeta_val, ite_eq_left (by omega : P.val < j), hP0]
    simp only [Nat.sub_zero]
  intro hpat
  rcases hpat with ⟨i1, i2, i3, i4, h12, h23, h34, g12, g23, g34⟩ |
    ⟨i1, i2, i3, i4, h12, h23, h34, g31, g42, g13⟩
  · have hocc := ntBeta_occur hj hPQ hκ h12 h23 h34 (Or.inl ⟨g12, g23, g34⟩)
    rcases hocc with ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩
    · have g13 : κ i1 < κ i3 := lt_trans g12 g23
      rw [← hP, ← hQ] at g13
      rw [Fin.lt_def, vP, vQ] at g13
      omega
    · have h3 : i3.val = 0 := by rw [← hP]; exact hP0
      omega
    · have h2 : i2.val = 0 := by rw [← hP]; exact hP0
      omega
    · have h4 : i4.val = 0 := by rw [← hP]; exact hP0
      omega
  · have hocc := ntBeta_occur hj hPQ hκ h12 h23 h34 (Or.inr ⟨g31, g42, g13⟩)
    rcases hocc with ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩
    · rw [← hQ] at g31
      rw [← hP] at g42
      rw [Fin.lt_def] at g31
      rw [Fin.lt_def] at g42
      rw [vQ] at g31
      rw [vP] at g42
      omega
    · have h3 : i3.val = 0 := by rw [← hP]; exact hP0
      omega
    · have h2 : i2.val = 0 := by rw [← hP]; exact hP0
      omega
    · have h4 : i4.val = 0 := by rw [← hP]; exact hP0
      omega

/-- The extreme pair `(j-1, n-1)` has no pattern: `kappa` takes the minimum. -/
private lemma ntK_noPat_C4 {n j : ℕ} (hj1 : 1 ≤ j) (hj : j + 1 ≤ n)
    {P Q : Fin n} (hPQ : P ≠ Q) (hPj : P.val = j - 1) (hQn : Q.val = n - 1)
    {κ : Equiv.Perm (Fin n)} (hκ : κ = ntBeta n j hj * Equiv.swap P Q) :
    ¬ ntPat n κ := by
  have vQ : (κ Q).val = 0 := by
    have eQ : κ Q = ntBeta n j hj P := by
      rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_right]
    have e : (κ Q).val = ((ntBeta n j hj) P).val := congrArg Fin.val eQ
    rw [e, ntBeta_val, ite_eq_left (by omega : P.val < j), hPj]
    omega
  intro hpat
  rcases hpat with ⟨i1, i2, i3, i4, h12, h23, h34, g12, g23, g34⟩ |
    ⟨i1, i2, i3, i4, h12, h23, h34, g31, g42, g13⟩
  · have hocc := ntBeta_occur hj hPQ hκ h12 h23 h34 (Or.inl ⟨g12, g23, g34⟩)
    rcases hocc with ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩
    · have h3 : i3.val = n - 1 := by rw [← hQ]; exact hQn
      have hi4 := (i4).is_lt
      omega
    · have h1 : i1.val = n - 1 := by rw [← hQ]; exact hQn
      have hi2 := (i2).is_lt
      omega
    · rw [← hQ] at g34
      rw [Fin.lt_def, vQ] at g34
      omega
    · have h2 : i2.val = n - 1 := by rw [← hQ]; exact hQn
      have hi3 := (i3).is_lt
      omega
  · have hocc := ntBeta_occur hj hPQ hκ h12 h23 h34 (Or.inr ⟨g31, g42, g13⟩)
    rcases hocc with ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩
    · have h3 : i3.val = n - 1 := by rw [← hQ]; exact hQn
      have hi4 := (i4).is_lt
      omega
    · have h1 : i1.val = n - 1 := by rw [← hQ]; exact hQn
      have hi2 := (i2).is_lt
      omega
    · rw [← hQ] at g31
      rw [Fin.lt_def, vQ] at g31
      omega
    · have h2 : i2.val = n - 1 := by rw [← hQ]; exact hQn
      have hi3 := (i3).is_lt
      omega

/-- When both hubs are live, the low hub reaches the high hub via `(1, n-2)`. -/
private lemma ntK_hubBridge {n j : ℕ} (hjn : j + 1 ≤ n) (hj3lo : 3 ≤ j)
    (hj3hi : j + 3 ≤ n)
    {Z J1 J N1 O N2 : Fin n} (hZ : Z.val = 0) (hJ1 : J1.val = j - 1)
    (hJ : J.val = j) (hN1 : N1.val = n - 1)
    (hO : O.val = 1) (hN2 : N2.val = n - 2) :
    Relation.EqvGen (ntMove n) (ntBeta n j hjn * Equiv.swap Z J1)
      (ntBeta n j hjn * Equiv.swap J N1) := by
  have hLowMid := ntK_lowHubMove (hj1 := by omega) hjn hZ hJ1 (U := O)
    (W := N2) (by omega) (by omega) (by omega) (rfl)
  have hHighMid := ntK_highHubMove (hj1 := by omega) hjn hJ hN1 (U := O)
    (W := N2) (by omega) (by omega) (by omega) (rfl)
  exact Relation.EqvGen.trans _ _ _ hLowMid
    (Relation.EqvGen.symm _ _ hHighMid)

/-- Hub reachability when `j ≤ 2`: every element routes via high moves. -/
private lemma ntK_hub_high_narrow {n j : ℕ} (hj1 : 1 ≤ j)
    (hjn : j + 1 ≤ n) (hj2 : j ≤ 2)
    {J N1 : Fin n} (hJ : J.val = j) (hN1 : N1.val = n - 1) :
    ∀ κ ∈ ntK n j hjn, Relation.EqvGen (ntMove n) κ
      (ntBeta n j hjn * Equiv.swap J N1) := by
  have hmix : ∀ {A B : Fin n}, A.val < j → j ≤ B.val →
      ∀ {μ : Equiv.Perm (Fin n)}, μ = ntBeta n j hjn * Equiv.swap A B →
        A ≠ B → ntPat n μ →
        Relation.EqvGen (ntMove n) μ (ntBeta n j hjn * Equiv.swap J N1) := by
    intro A B hAlow hBhigh μ hμT hAB hpat'
    by_cases hBj : B.val = j
    · by_cases hA0 : A.val = 0
      · exact absurd hpat' (ntK_noPat_C1 hjn hAB hA0 hBj hμT)
      · by_cases hAj : A.val = j - 1
        · have hadj : B.val = A.val + 1 := by omega
          exact absurd hpat' (ntK_noPat_adjacent hjn hAB (Or.inl hadj) hμT)
        · omega
    · by_cases hBn : B.val = n - 1
      · by_cases hA0 : A.val = 0
        · exact absurd hpat' (ntK_noPat_C2 hj1 hjn hAB hA0 hBn hμT)
        · by_cases hAj : A.val = j - 1
          · exact absurd hpat' (ntK_noPat_C4 hj1 hjn hAB hAj hBn hμT)
          · omega
      · have hBlt := B.is_lt
        have hBint : j < B.val ∧ B.val < n - 1 := by
          constructor <;> omega
        have hM4 := ntK_highHubMove hj1 hjn hJ hN1 (U := A) (W := B)
          hAlow hBint.1 hBint.2 (rfl)
        have hsym := Relation.EqvGen.symm _ _ hM4
        rw [hμT]
        exact hsym
  intro κ hκ
  obtain ⟨⟨P, Q, hPQ, hκT⟩, hpat⟩ := hκ
  by_cases hPlow : P.val < j <;> by_cases hQlow : Q.val < j
  · by_cases hPQlt : P.val < Q.val
    · by_cases hadj : Q.val = P.val + 1
      · exact absurd hpat (ntK_noPat_adjacent hjn hPQ (Or.inl hadj) hκT)
      · have hgap : P.val + 2 ≤ Q.val := by omega
        omega
    · by_cases hQP : Q.val < P.val
      · by_cases hadj : P.val = Q.val + 1
        · exact absurd hpat (ntK_noPat_adjacent hjn hPQ (Or.inr hadj) hκT)
        · have hgap : Q.val + 2 ≤ P.val := by omega
          omega
      · have heq : P.val = Q.val := by omega
        exact absurd (Fin.ext heq) hPQ
  · exact hmix hPlow (by omega) hκT hPQ hpat
  · have hκT' : κ = ntBeta n j hjn * Equiv.swap Q P := by
      rw [hκT, Equiv.swap_comm]
    exact hmix hQlow (by omega) hκT' (Ne.symm hPQ) hpat
  · by_cases hPQlt : P.val < Q.val
    · by_cases hadj : Q.val = P.val + 1
      · exact absurd hpat (ntK_noPat_adjacent hjn hPQ (Or.inl hadj) hκT)
      · have hgap : P.val + 2 ≤ Q.val := by omega
        have hPhigh : j ≤ P.val := by omega
        have hQhigh : j ≤ Q.val := by omega
        have hJ1lt : j - 1 < n := by omega
        have hP1lt : P.val + 1 < n := by have hQlt := Q.is_lt; omega
        have hM2 := ntK_highMove hj1 hjn hPhigh hQhigh hgap
          (J1 := ⟨j - 1, hJ1lt⟩) (P1 := ⟨P.val + 1, hP1lt⟩) rfl rfl hκT
        have hA : (⟨j - 1, hJ1lt⟩ : Fin n).val < j := by
          have hv : ((⟨j - 1, hJ1lt⟩ : Fin n)).val = j - 1 := rfl
          omega
        have hB1 : j < (⟨P.val + 1, hP1lt⟩ : Fin n).val := by
          have hv : ((⟨P.val + 1, hP1lt⟩ : Fin n)).val = P.val + 1 := rfl
          omega
        have hB2 : (⟨P.val + 1, hP1lt⟩ : Fin n).val < n - 1 := by
          have hv : ((⟨P.val + 1, hP1lt⟩ : Fin n)).val = P.val + 1 := rfl
          have hQlt := Q.is_lt
          omega
        have hM4 := ntK_highHubMove hj1 hjn hJ hN1
          (U := ⟨j - 1, hJ1lt⟩) (W := ⟨P.val + 1, hP1lt⟩) hA hB1 hB2 (rfl)
        exact Relation.EqvGen.trans _ _ _ hM2
          (Relation.EqvGen.symm _ _ hM4)
    · by_cases hQP : Q.val < P.val
      · by_cases hadj : P.val = Q.val + 1
        · exact absurd hpat (ntK_noPat_adjacent hjn hPQ (Or.inr hadj) hκT)
        · have hgap : Q.val + 2 ≤ P.val := by omega
          have hQhigh : j ≤ Q.val := by omega
          have hPhigh : j ≤ P.val := by omega
          have hJ1lt : j - 1 < n := by omega
          have hP1lt : Q.val + 1 < n := by have hPlt := P.is_lt; omega
          have hκT' : κ = ntBeta n j hjn * Equiv.swap Q P := by
            rw [hκT, Equiv.swap_comm]
          have hM2 := ntK_highMove hj1 hjn hQhigh hPhigh hgap
            (J1 := ⟨j - 1, hJ1lt⟩) (P1 := ⟨Q.val + 1, hP1lt⟩) rfl rfl hκT'
          have hA : (⟨j - 1, hJ1lt⟩ : Fin n).val < j := by
            have hv : ((⟨j - 1, hJ1lt⟩ : Fin n)).val = j - 1 := rfl
            omega
          have hB1 : j < (⟨Q.val + 1, hP1lt⟩ : Fin n).val := by
            have hv : ((⟨Q.val + 1, hP1lt⟩ : Fin n)).val = Q.val + 1 := rfl
            omega
          have hB2 : (⟨Q.val + 1, hP1lt⟩ : Fin n).val < n - 1 := by
            have hv : ((⟨Q.val + 1, hP1lt⟩ : Fin n)).val = Q.val + 1 := rfl
            have hPlt := P.is_lt
            omega
          have hM4 := ntK_highHubMove hj1 hjn hJ hN1
            (U := ⟨j - 1, hJ1lt⟩) (W := ⟨Q.val + 1, hP1lt⟩) hA hB1 hB2 (rfl)
          exact Relation.EqvGen.trans _ _ _ hM2
            (Relation.EqvGen.symm _ _ hM4)
      · have heq : P.val = Q.val := by omega
        exact absurd (Fin.ext heq) hPQ

/-- Hub reachability when `n - 2 ≤ j`: every element routes via low moves. -/
private lemma ntK_hub_low {n j : ℕ} (hj1 : 1 ≤ j)
    (hjn : j + 1 ≤ n) (hjn2 : n - 2 ≤ j)
    {Z J1 : Fin n} (hZ : Z.val = 0) (hJ1 : J1.val = j - 1) :
    ∀ κ ∈ ntK n j hjn, Relation.EqvGen (ntMove n) κ
      (ntBeta n j hjn * Equiv.swap Z J1) := by
  have hmix : ∀ {A B : Fin n}, A.val < j → j ≤ B.val →
      ∀ {μ : Equiv.Perm (Fin n)}, μ = ntBeta n j hjn * Equiv.swap A B →
        A ≠ B → ntPat n μ →
        Relation.EqvGen (ntMove n) μ (ntBeta n j hjn * Equiv.swap Z J1) := by
    intro A B hAlow hBhigh μ hμT hAB hpat'
    by_cases hBj : B.val = j
    · by_cases hA0 : A.val = 0
      · exact absurd hpat' (ntK_noPat_C1 hjn hAB hA0 hBj hμT)
      · by_cases hAj : A.val = j - 1
        · have hadj : B.val = A.val + 1 := by omega
          exact absurd hpat' (ntK_noPat_adjacent hjn hAB (Or.inl hadj) hμT)
        · have hA0' : 0 < A.val := by omega
          have hAj' : A.val < j - 1 := by omega
          have hBhigh' : j ≤ B.val := by omega
          have hM3 := ntK_lowHubMove hj1 hjn hZ hJ1 (U := A) (W := B)
            hA0' hAj' hBhigh' (rfl)
          have hsym := Relation.EqvGen.symm _ _ hM3
          rw [hμT]
          exact hsym
    · by_cases hBn : B.val = n - 1
      · by_cases hA0 : A.val = 0
        · exact absurd hpat' (ntK_noPat_C2 hj1 hjn hAB hA0 hBn hμT)
        · by_cases hAj : A.val = j - 1
          · exact absurd hpat' (ntK_noPat_C4 hj1 hjn hAB hAj hBn hμT)
          · have hA0' : 0 < A.val := by omega
            have hAj' : A.val < j - 1 := by omega
            have hBhigh' : j ≤ B.val := by omega
            have hM3 := ntK_lowHubMove hj1 hjn hZ hJ1 (U := A) (W := B)
              hA0' hAj' hBhigh' (rfl)
            have hsym := Relation.EqvGen.symm _ _ hM3
            rw [hμT]
            exact hsym
      · have hBlt := B.is_lt
        omega
  intro κ hκ
  obtain ⟨⟨P, Q, hPQ, hκT⟩, hpat⟩ := hκ
  by_cases hPlow : P.val < j <;> by_cases hQlow : Q.val < j
  · by_cases hPQlt : P.val < Q.val
    · by_cases hadj : Q.val = P.val + 1
      · exact absurd hpat (ntK_noPat_adjacent hjn hPQ (Or.inl hadj) hκT)
      · have hgap : P.val + 2 ≤ Q.val := by omega
        have hP1lt : P.val + 1 < n := by have hQlt := Q.is_lt; omega
        have hJlt : j < n := by omega
        have hM1 := ntK_lowMove hjn hPlow hQlow hgap
          (P1 := ⟨P.val + 1, hP1lt⟩) (J := ⟨j, hJlt⟩) rfl rfl hκT
        have hA : 0 < (⟨P.val + 1, hP1lt⟩ : Fin n).val := by
          have hv : ((⟨P.val + 1, hP1lt⟩ : Fin n)).val = P.val + 1 := rfl
          omega
        have hAj : (⟨P.val + 1, hP1lt⟩ : Fin n).val < j - 1 := by
          have hv : ((⟨P.val + 1, hP1lt⟩ : Fin n)).val = P.val + 1 := rfl
          omega
        have hBj : j ≤ (⟨j, hJlt⟩ : Fin n).val := by
          have hv : ((⟨j, hJlt⟩ : Fin n)).val = j := rfl
          omega
        have hM3 := ntK_lowHubMove hj1 hjn hZ hJ1
          (U := ⟨P.val + 1, hP1lt⟩) (W := ⟨j, hJlt⟩) hA hAj hBj (rfl)
        exact Relation.EqvGen.trans _ _ _ hM1
          (Relation.EqvGen.symm _ _ hM3)
    · by_cases hQP : Q.val < P.val
      · by_cases hadj : P.val = Q.val + 1
        · exact absurd hpat (ntK_noPat_adjacent hjn hPQ (Or.inr hadj) hκT)
        · have hgap : Q.val + 2 ≤ P.val := by omega
          have hP1lt : Q.val + 1 < n := by have hPlt := P.is_lt; omega
          have hJlt : j < n := by omega
          have hκT' : κ = ntBeta n j hjn * Equiv.swap Q P := by
            rw [hκT, Equiv.swap_comm]
          have hM1 := ntK_lowMove hjn hQlow hPlow hgap
            (P1 := ⟨Q.val + 1, hP1lt⟩) (J := ⟨j, hJlt⟩) rfl rfl hκT'
          have hA : 0 < (⟨Q.val + 1, hP1lt⟩ : Fin n).val := by
            have hv : ((⟨Q.val + 1, hP1lt⟩ : Fin n)).val = Q.val + 1 := rfl
            omega
          have hAj : (⟨Q.val + 1, hP1lt⟩ : Fin n).val < j - 1 := by
            have hv : ((⟨Q.val + 1, hP1lt⟩ : Fin n)).val = Q.val + 1 := rfl
            omega
          have hBj : j ≤ (⟨j, hJlt⟩ : Fin n).val := by
            have hv : ((⟨j, hJlt⟩ : Fin n)).val = j := rfl
            omega
          have hM3 := ntK_lowHubMove hj1 hjn hZ hJ1
            (U := ⟨Q.val + 1, hP1lt⟩) (W := ⟨j, hJlt⟩) hA hAj hBj (rfl)
          exact Relation.EqvGen.trans _ _ _ hM1
            (Relation.EqvGen.symm _ _ hM3)
      · have heq : P.val = Q.val := by omega
        exact absurd (Fin.ext heq) hPQ
  · exact hmix hPlow (by omega) hκT hPQ hpat
  · have hκT' : κ = ntBeta n j hjn * Equiv.swap Q P := by
      rw [hκT, Equiv.swap_comm]
    exact hmix hQlow (by omega) hκT' (Ne.symm hPQ) hpat
  · by_cases hPQlt : P.val < Q.val
    · by_cases hadj : Q.val = P.val + 1
      · exact absurd hpat (ntK_noPat_adjacent hjn hPQ (Or.inl hadj) hκT)
      · have hgap : P.val + 2 ≤ Q.val := by omega
        have hQlt := Q.is_lt
        omega
    · by_cases hQP : Q.val < P.val
      · by_cases hadj : P.val = Q.val + 1
        · exact absurd hpat (ntK_noPat_adjacent hjn hPQ (Or.inr hadj) hκT)
        · have hgap : Q.val + 2 ≤ P.val := by omega
          have hPlt := P.is_lt
          omega
      · have heq : P.val = Q.val := by omega
        exact absurd (Fin.ext heq) hPQ

/-- Hub reachability when `3 ≤ j` and `j + 3 ≤ n`: full scheme with bridge. -/
private lemma ntK_hub_high_wide {n j : ℕ} (hj1 : 1 ≤ j)
    (hjn : j + 1 ≤ n) (hj3lo : 3 ≤ j) (hj3hi : j + 3 ≤ n)
    {J N1 Z J1 O N2 : Fin n} (hJ : J.val = j) (hN1 : N1.val = n - 1)
    (hZ : Z.val = 0) (hJ1 : J1.val = j - 1)
    (hO : O.val = 1) (hN2 : N2.val = n - 2) :
    ∀ κ ∈ ntK n j hjn, Relation.EqvGen (ntMove n) κ
      (ntBeta n j hjn * Equiv.swap J N1) := by
  have hBridge := ntK_hubBridge hjn hj3lo hj3hi hZ hJ1 hJ hN1 hO hN2
  have hmix : ∀ {A B : Fin n}, A.val < j → j ≤ B.val →
      ∀ {μ : Equiv.Perm (Fin n)}, μ = ntBeta n j hjn * Equiv.swap A B →
        A ≠ B → ntPat n μ →
        Relation.EqvGen (ntMove n) μ (ntBeta n j hjn * Equiv.swap J N1) := by
    intro A B hAlow hBhigh μ hμT hAB hpat'
    by_cases hBj : B.val = j
    · by_cases hA0 : A.val = 0
      · exact absurd hpat' (ntK_noPat_C1 hjn hAB hA0 hBj hμT)
      · by_cases hAj : A.val = j - 1
        · have hadj : B.val = A.val + 1 := by omega
          exact absurd hpat' (ntK_noPat_adjacent hjn hAB (Or.inl hadj) hμT)
        · have hA0' : 0 < A.val := by omega
          have hAj' : A.val < j - 1 := by omega
          have hBhigh' : j ≤ B.val := by omega
          have hM3 := ntK_lowHubMove hj1 hjn hZ hJ1 (U := A) (W := B)
            hA0' hAj' hBhigh' (rfl)
          have h1 := Relation.EqvGen.symm _ _ hM3
          rw [hμT]
          exact Relation.EqvGen.trans _ _ _ h1 hBridge
    · by_cases hBn : B.val = n - 1
      · by_cases hA0 : A.val = 0
        · exact absurd hpat' (ntK_noPat_C2 hj1 hjn hAB hA0 hBn hμT)
        · by_cases hAj : A.val = j - 1
          · exact absurd hpat' (ntK_noPat_C4 hj1 hjn hAB hAj hBn hμT)
          · have hA0' : 0 < A.val := by omega
            have hAj' : A.val < j - 1 := by omega
            have hBhigh' : j ≤ B.val := by omega
            have hM3 := ntK_lowHubMove hj1 hjn hZ hJ1 (U := A) (W := B)
              hA0' hAj' hBhigh' (rfl)
            have h1 := Relation.EqvGen.symm _ _ hM3
            rw [hμT]
            exact Relation.EqvGen.trans _ _ _ h1 hBridge
      · have hBlt := B.is_lt
        have hBint : j < B.val ∧ B.val < n - 1 := by
          constructor <;> omega
        have hM4 := ntK_highHubMove hj1 hjn hJ hN1 (U := A) (W := B)
          hAlow hBint.1 hBint.2 (rfl)
        have hsym := Relation.EqvGen.symm _ _ hM4
        rw [hμT]
        exact hsym
  intro κ hκ
  obtain ⟨⟨P, Q, hPQ, hκT⟩, hpat⟩ := hκ
  by_cases hPlow : P.val < j <;> by_cases hQlow : Q.val < j
  · by_cases hPQlt : P.val < Q.val
    · by_cases hadj : Q.val = P.val + 1
      · exact absurd hpat (ntK_noPat_adjacent hjn hPQ (Or.inl hadj) hκT)
      · have hgap : P.val + 2 ≤ Q.val := by omega
        have hP1lt : P.val + 1 < n := by have hQlt := Q.is_lt; omega
        have hJlt : j < n := by omega
        have hM1 := ntK_lowMove hjn hPlow hQlow hgap
          (P1 := ⟨P.val + 1, hP1lt⟩) (J := ⟨j, hJlt⟩) rfl rfl hκT
        have hA : 0 < (⟨P.val + 1, hP1lt⟩ : Fin n).val := by
          have hv : ((⟨P.val + 1, hP1lt⟩ : Fin n)).val = P.val + 1 := rfl
          omega
        have hAj : (⟨P.val + 1, hP1lt⟩ : Fin n).val < j - 1 := by
          have hv : ((⟨P.val + 1, hP1lt⟩ : Fin n)).val = P.val + 1 := rfl
          omega
        have hBj : j ≤ (⟨j, hJlt⟩ : Fin n).val := by
          have hv : ((⟨j, hJlt⟩ : Fin n)).val = j := rfl
          omega
        have hM3 := ntK_lowHubMove hj1 hjn hZ hJ1
          (U := ⟨P.val + 1, hP1lt⟩) (W := ⟨j, hJlt⟩) hA hAj hBj (rfl)
        exact Relation.EqvGen.trans _ _ _ hM1
          (Relation.EqvGen.trans _ _ _
            (Relation.EqvGen.symm _ _ hM3) hBridge)
    · by_cases hQP : Q.val < P.val
      · by_cases hadj : P.val = Q.val + 1
        · exact absurd hpat (ntK_noPat_adjacent hjn hPQ (Or.inr hadj) hκT)
        · have hgap : Q.val + 2 ≤ P.val := by omega
          have hP1lt : Q.val + 1 < n := by have hPlt := P.is_lt; omega
          have hJlt : j < n := by omega
          have hκT' : κ = ntBeta n j hjn * Equiv.swap Q P := by
            rw [hκT, Equiv.swap_comm]
          have hM1 := ntK_lowMove hjn hQlow hPlow hgap
            (P1 := ⟨Q.val + 1, hP1lt⟩) (J := ⟨j, hJlt⟩) rfl rfl hκT'
          have hA : 0 < (⟨Q.val + 1, hP1lt⟩ : Fin n).val := by
            have hv : ((⟨Q.val + 1, hP1lt⟩ : Fin n)).val = Q.val + 1 := rfl
            omega
          have hAj : (⟨Q.val + 1, hP1lt⟩ : Fin n).val < j - 1 := by
            have hv : ((⟨Q.val + 1, hP1lt⟩ : Fin n)).val = Q.val + 1 := rfl
            omega
          have hBj : j ≤ (⟨j, hJlt⟩ : Fin n).val := by
            have hv : ((⟨j, hJlt⟩ : Fin n)).val = j := rfl
            omega
          have hM3 := ntK_lowHubMove hj1 hjn hZ hJ1
            (U := ⟨Q.val + 1, hP1lt⟩) (W := ⟨j, hJlt⟩) hA hAj hBj (rfl)
          exact Relation.EqvGen.trans _ _ _ hM1
            (Relation.EqvGen.trans _ _ _
              (Relation.EqvGen.symm _ _ hM3) hBridge)
      · have heq : P.val = Q.val := by omega
        exact absurd (Fin.ext heq) hPQ
  · exact hmix hPlow (by omega) hκT hPQ hpat
  · have hκT' : κ = ntBeta n j hjn * Equiv.swap Q P := by
      rw [hκT, Equiv.swap_comm]
    exact hmix hQlow (by omega) hκT' (Ne.symm hPQ) hpat
  · by_cases hPQlt : P.val < Q.val
    · by_cases hadj : Q.val = P.val + 1
      · exact absurd hpat (ntK_noPat_adjacent hjn hPQ (Or.inl hadj) hκT)
      · have hgap : P.val + 2 ≤ Q.val := by omega
        have hPhigh : j ≤ P.val := by omega
        have hQhigh : j ≤ Q.val := by omega
        have hJ1lt : j - 1 < n := by omega
        have hP1lt : P.val + 1 < n := by have hQlt := Q.is_lt; omega
        have hM2 := ntK_highMove hj1 hjn hPhigh hQhigh hgap
          (J1 := ⟨j - 1, hJ1lt⟩) (P1 := ⟨P.val + 1, hP1lt⟩) rfl rfl hκT
        have hA : (⟨j - 1, hJ1lt⟩ : Fin n).val < j := by
          have hv : ((⟨j - 1, hJ1lt⟩ : Fin n)).val = j - 1 := rfl
          omega
        have hB1 : j < (⟨P.val + 1, hP1lt⟩ : Fin n).val := by
          have hv : ((⟨P.val + 1, hP1lt⟩ : Fin n)).val = P.val + 1 := rfl
          omega
        have hB2 : (⟨P.val + 1, hP1lt⟩ : Fin n).val < n - 1 := by
          have hv : ((⟨P.val + 1, hP1lt⟩ : Fin n)).val = P.val + 1 := rfl
          have hQlt := Q.is_lt
          omega
        have hM4 := ntK_highHubMove hj1 hjn hJ hN1
          (U := ⟨j - 1, hJ1lt⟩) (W := ⟨P.val + 1, hP1lt⟩) hA hB1 hB2 (rfl)
        exact Relation.EqvGen.trans _ _ _ hM2
          (Relation.EqvGen.symm _ _ hM4)
    · by_cases hQP : Q.val < P.val
      · by_cases hadj : P.val = Q.val + 1
        · exact absurd hpat (ntK_noPat_adjacent hjn hPQ (Or.inr hadj) hκT)
        · have hgap : Q.val + 2 ≤ P.val := by omega
          have hQhigh : j ≤ Q.val := by omega
          have hPhigh : j ≤ P.val := by omega
          have hJ1lt : j - 1 < n := by omega
          have hP1lt : Q.val + 1 < n := by have hPlt := P.is_lt; omega
          have hκT' : κ = ntBeta n j hjn * Equiv.swap Q P := by
            rw [hκT, Equiv.swap_comm]
          have hM2 := ntK_highMove hj1 hjn hQhigh hPhigh hgap
            (J1 := ⟨j - 1, hJ1lt⟩) (P1 := ⟨Q.val + 1, hP1lt⟩) rfl rfl hκT'
          have hA : (⟨j - 1, hJ1lt⟩ : Fin n).val < j := by
            have hv : ((⟨j - 1, hJ1lt⟩ : Fin n)).val = j - 1 := rfl
            omega
          have hB1 : j < (⟨Q.val + 1, hP1lt⟩ : Fin n).val := by
            have hv : ((⟨Q.val + 1, hP1lt⟩ : Fin n)).val = Q.val + 1 := rfl
            omega
          have hB2 : (⟨Q.val + 1, hP1lt⟩ : Fin n).val < n - 1 := by
            have hv : ((⟨Q.val + 1, hP1lt⟩ : Fin n)).val = Q.val + 1 := rfl
            have hPlt := P.is_lt
            omega
          have hM4 := ntK_highHubMove hj1 hjn hJ hN1
            (U := ⟨j - 1, hJ1lt⟩) (W := ⟨Q.val + 1, hP1lt⟩) hA hB1 hB2 (rfl)
          exact Relation.EqvGen.trans _ _ _ hM2
            (Relation.EqvGen.symm _ _ hM4)
      · have heq : P.val = Q.val := by omega
        exact absurd (Fin.ext heq) hPQ

/-- Each `K` has a hub reaching every element. -/
private lemma ntK_hub {n j : ℕ} (hn : 5 ≤ n) (hj1 : 1 ≤ j) (hjn : j + 1 ≤ n) :
    ∃ hub ∈ ntK n j hjn,
      ∀ κ ∈ ntK n j hjn, Relation.EqvGen (ntMove n) κ hub := by
  have hJlt : j < n := by omega
  have hN1lt : n - 1 < n := by omega
  have h0lt : 0 < n := by omega
  have hJ1lt : j - 1 < n := by omega
  have hOlt : 1 < n := by omega
  have hN2lt : n - 2 < n := by omega
  have hJv : ((⟨j, hJlt⟩ : Fin n)).val = j := rfl
  have hN1v : ((⟨n - 1, hN1lt⟩ : Fin n)).val = n - 1 := rfl
  have hZv : ((⟨0, h0lt⟩ : Fin n)).val = 0 := rfl
  have hJ1v : ((⟨j - 1, hJ1lt⟩ : Fin n)).val = j - 1 := rfl
  have hOv : ((⟨1, hOlt⟩ : Fin n)).val = 1 := rfl
  have hN2v : ((⟨n - 2, hN2lt⟩ : Fin n)).val = n - 2 := rfl
  by_cases hj3 : j + 3 ≤ n
  · refine ⟨ntBeta n j hjn * Equiv.swap ⟨j, hJlt⟩ ⟨n - 1, hN1lt⟩,
      ⟨⟨⟨j, hJlt⟩, ⟨n - 1, hN1lt⟩, ?_, rfl⟩, ?_⟩, ?_⟩
    · exact Fin.ne_of_val_ne (by omega)
    · exact ntK_highHub_pat hn hj1 hjn hj3 hJv hN1v
    · by_cases hj2 : j ≤ 2
      · exact ntK_hub_high_narrow hj1 hjn hj2 hJv hN1v
      · have hj3lo : 3 ≤ j := by omega
        exact ntK_hub_high_wide hj1 hjn hj3lo hj3
          hJv hN1v hZv hJ1v hOv hN2v
  · have hjn2 : n - 2 ≤ j := by omega
    have hj3lo : 3 ≤ j := by omega
    refine ⟨ntBeta n j hjn * Equiv.swap ⟨0, h0lt⟩ ⟨j - 1, hJ1lt⟩,
      ⟨⟨⟨0, h0lt⟩, ⟨j - 1, hJ1lt⟩, ?_, rfl⟩, ?_⟩, ?_⟩
    · exact Fin.ne_of_val_ne (by omega)
    · exact ntK_lowHub_pat hn hjn hj3lo hZv hJ1v
    · exact ntK_hub_low hj1 hjn hjn2 hZv hJ1v

/-- The residue class forced by the two-block shape. -/
private lemma ntBeta_residue {n j : ℕ} (hj1 : 1 ≤ j) (hj : j + 1 ≤ n)
    (i : Fin n) :
    Nat.ModEq n (((ntBeta n j hj) i).val + i.val) (j - 1) := by
  rw [ntBeta_val hj]
  by_cases h : i.val < j
  · rw [ite_eq_left h]
    have e : j - 1 - i.val + i.val = j - 1 := by omega
    rw [e]
  · rw [ite_eq_right h]
    have e : n + j - 1 - i.val + i.val = n + j - 1 := by
      have := i.is_lt
      omega
    have e2 : n + j - 1 = n + (j - 1) := by omega
    rw [e, e2]
    change (n + (j - 1)) % n = (j - 1) % n
    rw [Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod]

/-- Different `K`s are disjoint. -/
private lemma ntK_disjoint {n j k : ℕ} (hn : 5 ≤ n)
    (hj1 : 1 ≤ j) (hjn : j + 1 ≤ n) (hk1 : 1 ≤ k) (hkn : k + 1 ≤ n)
    (hjk : j ≠ k) : Disjoint (ntK n j hjn) (ntK n k hkn) := by
  rw [Set.disjoint_left]
  intro κ hκJ hκK
  obtain ⟨⟨P, Q, hPQ, hκTj⟩, _⟩ := hκJ
  obtain ⟨⟨P', Q', hPQ', hκTk⟩, _⟩ := hκK
  have hcard : ({P, Q, P', Q'} : Finset (Fin n)).card ≤ 4 :=
    calc ({P, Q, P', Q'} : Finset (Fin n)).card
        ≤ ({Q, P', Q'} : Finset (Fin n)).card + 1 :=
          Finset.card_insert_le _ _
      _ ≤ ((({P', Q'} : Finset (Fin n)).card + 1) + 1) :=
          Nat.add_le_add_right (Finset.card_insert_le _ _) _
      _ ≤ ((((({Q'} : Finset (Fin n)).card + 1) + 1) + 1)) :=
          Nat.add_le_add_right
            (Nat.add_le_add_right (Finset.card_insert_le _ _) _) _
      _ = 4 := by simp
  have hne : ({P, Q, P', Q'} : Finset (Fin n)) ≠ Finset.univ := by
    intro hcon
    have hcc := congrArg Finset.card hcon
    rw [Finset.card_univ, Fintype.card_fin] at hcc
    omega
  have hss : ({P, Q, P', Q'} : Finset (Fin n)) ⊂ Finset.univ :=
    Finset.ssubset_univ_iff.mpr hne
  obtain ⟨i, -, hi⟩ := Finset.exists_of_ssubset hss
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
  obtain ⟨hiP, hiQ, hiP', hiQ'⟩ := hi
  have eJ : κ i = ntBeta n j hjn i := by
    rw [hκTj, Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne hiP hiQ]
  have eK : κ i = ntBeta n k hkn i := by
    rw [hκTk, Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne hiP' hiQ']
  have eJv : (κ i).val = ((ntBeta n j hjn) i).val := congrArg Fin.val eJ
  have eKv : (κ i).val = ((ntBeta n k hkn) i).val := congrArg Fin.val eK
  have rJ := ntBeta_residue hj1 hjn i
  have rK := ntBeta_residue hk1 hkn i
  rw [← eJv] at rJ
  rw [← eKv] at rK
  have hmod : (j - 1) % n = (k - 1) % n := rJ.symm.trans rK
  rw [Nat.mod_eq_of_lt (show j - 1 < n by omega),
    Nat.mod_eq_of_lt (show k - 1 < n by omega)] at hmod
  omega

/-- Each `K` lies inside the extreme-avoiding set. -/
private lemma ntK_sub_E {m j : ℕ} (hj1 : 1 ≤ j) (hjn : j + 1 ≤ m + 2) :
    ntK (m + 2) j hjn ⊆ ntE (m + 1) := by
  intro κ hκ
  obtain ⟨⟨P, Q, hPQ, hκT⟩, hκP⟩ := hκ
  have hlastv : (Fin.last (m + 1) : Fin (m + 2)).val = m + 1 := Fin.val_last _
  have h0v : ((0 : Fin (m + 2))).val = 0 := Fin.val_zero _
  have hc0 : ((0 : Fin (m + 2))).val < j := by rw [h0v]; omega
  have beta0 : ((ntBeta (m + 2) j hjn) 0).val = j - 1 := by
    rw [ntBeta_val hjn, ite_eq_left hc0, h0v, Nat.sub_zero]
  have hlastlt : ¬ ((Fin.last (m + 1) : Fin (m + 2))).val < j := by
    rw [hlastv]; omega
  have betaLast : ((ntBeta (m + 2) j hjn) (Fin.last (m + 1))).val = j := by
    rw [ntBeta_val hjn, ite_eq_right hlastlt, hlastv]
    omega
  constructor
  · intro h0
    have hmax : (κ 0).val = m + 1 := by rw [h0]; exact hlastv
    have h0mem : (0 : Fin (m + 2)) = P ∨ (0 : Fin (m + 2)) = Q := by
      by_contra hcon
      simp only [not_or] at hcon
      obtain ⟨nP, nQ⟩ := hcon
      have hS0 : Equiv.swap P Q (0 : Fin (m + 2)) = 0 :=
        Equiv.swap_apply_of_ne_of_ne nP nQ
      have e : κ 0 = ntBeta (m + 2) j hjn 0 := by
        rw [hκT, Equiv.Perm.mul_apply, hS0]
      have ev : (κ 0).val = j - 1 := by rw [e]; exact beta0
      rw [ev] at hmax
      omega
    rcases hκP with h1234 | h3412
    · obtain ⟨i1, i2, i3, i4, h12, h23, h34, g12, g23, g34⟩ := h1234
      have hocc := ntBeta_occur hjn hPQ hκT h12 h23 h34 (Or.inl ⟨g12, g23, g34⟩)
      rcases hocc with ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩
      · rcases h0mem with h0' | h0'
        · rw [hP] at h0'
          have hr : (κ i1).val = m + 1 := by rw [← h0']; exact hmax
          have hlt : (κ i1).val < (κ i2).val := Fin.lt_def.mp g12
          have hle : (κ i2).val ≤ m + 1 := by
            have := (κ i2).is_lt; omega
          omega
        · rw [hQ] at h0'
          have hr : (κ i3).val = m + 1 := by rw [← h0']; exact hmax
          have hlt : (κ i3).val < (κ i4).val := Fin.lt_def.mp g34
          have hle : (κ i4).val ≤ m + 1 := by
            have := (κ i4).is_lt; omega
          omega
      · rcases h0mem with h0' | h0'
        · rw [hP] at h0'
          have hr : (κ i3).val = m + 1 := by rw [← h0']; exact hmax
          have hlt : (κ i3).val < (κ i4).val := Fin.lt_def.mp g34
          have hle : (κ i4).val ≤ m + 1 := by
            have := (κ i4).is_lt; omega
          omega
        · rw [hQ] at h0'
          have hr : (κ i1).val = m + 1 := by rw [← h0']; exact hmax
          have hlt : (κ i1).val < (κ i2).val := Fin.lt_def.mp g12
          have hle : (κ i2).val ≤ m + 1 := by
            have := (κ i2).is_lt; omega
          omega
      · rcases h0mem with h0' | h0'
        · rw [hP] at h0'
          have hr : (κ i2).val = m + 1 := by rw [← h0']; exact hmax
          have hlt : (κ i2).val < (κ i3).val := Fin.lt_def.mp g23
          have hle : (κ i3).val ≤ m + 1 := by
            have := (κ i3).is_lt; omega
          omega
        · rw [hQ] at h0'
          rw [← h0'] at h34
          rw [h0v] at h34
          omega
      · rcases h0mem with h0' | h0'
        · rw [hP] at h0'
          rw [← h0'] at h34
          rw [h0v] at h34
          omega
        · rw [hQ] at h0'
          have hr : (κ i2).val = m + 1 := by rw [← h0']; exact hmax
          have hlt : (κ i2).val < (κ i3).val := Fin.lt_def.mp g23
          have hle : (κ i3).val ≤ m + 1 := by
            have := (κ i3).is_lt; omega
          omega
    · obtain ⟨i1, i2, i3, i4, h12, h23, h34, g31, g42, g13⟩ := h3412
      have hocc := ntBeta_occur hjn hPQ hκT h12 h23 h34
        (Or.inr ⟨g31, g42, g13⟩)
      rcases hocc with ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩
      · rcases h0mem with h0' | h0'
        · rw [hP] at h0'
          have hr : (κ i1).val = m + 1 := by rw [← h0']; exact hmax
          have hlt : (κ i1).val < (κ i2).val := Fin.lt_def.mp g13
          have hle : (κ i2).val ≤ m + 1 := by
            have := (κ i2).is_lt; omega
          omega
        · rw [hQ] at h0'
          have hr : (κ i3).val = m + 1 := by rw [← h0']; exact hmax
          have hlt : (κ i3).val < (κ i4).val := Fin.lt_def.mp g31
          have hle : (κ i4).val ≤ m + 1 := by
            have := (κ i4).is_lt; omega
          omega
      · rcases h0mem with h0' | h0'
        · rw [hP] at h0'
          have hr : (κ i3).val = m + 1 := by rw [← h0']; exact hmax
          have hlt : (κ i3).val < (κ i4).val := Fin.lt_def.mp g31
          have hle : (κ i4).val ≤ m + 1 := by
            have := (κ i4).is_lt; omega
          omega
        · rw [hQ] at h0'
          have hr : (κ i1).val = m + 1 := by rw [← h0']; exact hmax
          have hlt : (κ i1).val < (κ i2).val := Fin.lt_def.mp g13
          have hle : (κ i2).val ≤ m + 1 := by
            have := (κ i2).is_lt; omega
          omega
      · rcases h0mem with h0' | h0'
        · rw [hP] at h0'
          rw [← h0'] at h12
          rw [h0v] at h12
          omega
        · rw [hQ] at h0'
          have hr : (κ i4).val = m + 1 := by rw [← h0']; exact hmax
          have hlt : (κ i4).val < (κ i1).val := Fin.lt_def.mp g42
          have hle : (κ i1).val ≤ m + 1 := by
            have := (κ i1).is_lt; omega
          omega
      · rcases h0mem with h0' | h0'
        · rw [hP] at h0'
          have hr : (κ i4).val = m + 1 := by rw [← h0']; exact hmax
          have hlt : (κ i4).val < (κ i1).val := Fin.lt_def.mp g42
          have hle : (κ i1).val ≤ m + 1 := by
            have := (κ i1).is_lt; omega
          omega
        · rw [hQ] at h0'
          rw [← h0'] at h12
          rw [h0v] at h12
          omega
  · intro hlast
    have hmin : (κ (Fin.last (m + 1))).val = 0 := by rw [hlast]; exact h0v
    have hlastmem : Fin.last (m + 1) = P ∨ Fin.last (m + 1) = Q := by
      by_contra hcon
      simp only [not_or] at hcon
      obtain ⟨nP, nQ⟩ := hcon
      have hSl : Equiv.swap P Q (Fin.last (m + 1)) = Fin.last (m + 1) :=
        Equiv.swap_apply_of_ne_of_ne nP nQ
      have e : κ (Fin.last (m + 1)) = ntBeta (m + 2) j hjn (Fin.last (m + 1)) := by
        rw [hκT, Equiv.Perm.mul_apply, hSl]
      have ev : (κ (Fin.last (m + 1))).val = j := by rw [e]; exact betaLast
      rw [ev] at hmin
      omega
    rcases hκP with h1234 | h3412
    · obtain ⟨i1, i2, i3, i4, h12, h23, h34, g12, g23, g34⟩ := h1234
      have hocc := ntBeta_occur hjn hPQ hκT h12 h23 h34 (Or.inl ⟨g12, g23, g34⟩)
      rcases hocc with ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩
      · rcases hlastmem with hl' | hl'
        · rw [hP] at hl'
          rw [← hl'] at h12
          rw [hlastv] at h12
          have hle : i2.val ≤ m + 1 := by
            have := i2.is_lt; omega
          omega
        · rw [hQ] at hl'
          have hr : (κ i3).val = 0 := by rw [← hl']; exact hmin
          have hlt : (κ i2).val < (κ i3).val := Fin.lt_def.mp g23
          omega
      · rcases hlastmem with hl' | hl'
        · rw [hP] at hl'
          have hr : (κ i3).val = 0 := by rw [← hl']; exact hmin
          have hlt : (κ i2).val < (κ i3).val := Fin.lt_def.mp g23
          omega
        · rw [hQ] at hl'
          rw [← hl'] at h12
          rw [hlastv] at h12
          have hle : i2.val ≤ m + 1 := by
            have := i2.is_lt; omega
          omega
      · rcases hlastmem with hl' | hl'
        · rw [hP] at hl'
          have hr : (κ i2).val = 0 := by rw [← hl']; exact hmin
          have hlt : (κ i1).val < (κ i2).val := Fin.lt_def.mp g12
          omega
        · rw [hQ] at hl'
          have hr : (κ i4).val = 0 := by rw [← hl']; exact hmin
          have hlt : (κ i3).val < (κ i4).val := Fin.lt_def.mp g34
          omega
      · rcases hlastmem with hl' | hl'
        · rw [hP] at hl'
          have hr : (κ i4).val = 0 := by rw [← hl']; exact hmin
          have hlt : (κ i3).val < (κ i4).val := Fin.lt_def.mp g34
          omega
        · rw [hQ] at hl'
          have hr : (κ i2).val = 0 := by rw [← hl']; exact hmin
          have hlt : (κ i1).val < (κ i2).val := Fin.lt_def.mp g12
          omega
    · obtain ⟨i1, i2, i3, i4, h12, h23, h34, g31, g42, g13⟩ := h3412
      have hocc := ntBeta_occur hjn hPQ hκT h12 h23 h34
        (Or.inr ⟨g31, g42, g13⟩)
      rcases hocc with ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩
      · rcases hlastmem with hl' | hl'
        · rw [hP] at hl'
          have hr : (κ i1).val = 0 := by rw [← hl']; exact hmin
          have hlt : (κ i4).val < (κ i1).val := Fin.lt_def.mp g42
          omega
        · rw [hQ] at hl'
          rw [← hl'] at h34
          rw [hlastv] at h34
          have hle : i4.val ≤ m + 1 := by
            have := i4.is_lt; omega
          omega
      · rcases hlastmem with hl' | hl'
        · rw [hP] at hl'
          rw [← hl'] at h34
          rw [hlastv] at h34
          have hle : i4.val ≤ m + 1 := by
            have := i4.is_lt; omega
          omega
        · rw [hQ] at hl'
          have hr : (κ i1).val = 0 := by rw [← hl']; exact hmin
          have hlt : (κ i4).val < (κ i1).val := Fin.lt_def.mp g42
          omega
      · rcases hlastmem with hl' | hl'
        · rw [hP] at hl'
          have hr : (κ i2).val = 0 := by rw [← hl']; exact hmin
          have hlt : (κ i1).val < (κ i2).val := Fin.lt_def.mp g13
          omega
        · rw [hQ] at hl'
          have hr : (κ i4).val = 0 := by rw [← hl']; exact hmin
          have hlt : (κ i3).val < (κ i4).val := Fin.lt_def.mp g31
          omega
      · rcases hlastmem with hl' | hl'
        · rw [hP] at hl'
          have hr : (κ i4).val = 0 := by rw [← hl']; exact hmin
          have hlt : (κ i3).val < (κ i4).val := Fin.lt_def.mp g31
          omega
        · rw [hQ] at hl'
          have hr : (κ i2).val = 0 := by rw [← hl']; exact hmin
          have hlt : (κ i1).val < (κ i2).val := Fin.lt_def.mp g13
          omega

/-- An increasing 5-subsequence rules out every `K`. -/
private lemma ntInc5_notK {k j : ℕ} (_hk : 5 ≤ k + 2) (_hj1 : 1 ≤ j)
    (hjn : j + 1 ≤ k + 2) {σ : Equiv.Perm (Fin (k + 2))}
    (h : ntInc5 (k + 2) σ) : σ ∉ ntK (k + 2) j hjn := by
  intro hσ
  obtain ⟨a, b, c, d, e, hab, hbc, hcd, hde, vab, vbc, vcd, vde⟩ := h
  obtain ⟨⟨P, Q, _hPQ, hσT⟩, -⟩ := hσ
  have hac : a.val < c.val := lt_trans hab hbc
  have hbd : b.val < d.val := lt_trans hbc hcd
  have hce : c.val < e.val := lt_trans hcd hde
  have had : a.val < d.val := lt_trans hab hbd
  have hbe : b.val < e.val := lt_trans hbc hce
  have hae : a.val < e.val := lt_trans hab hbe
  have dab : a ≠ b := by intro h; subst h; exact lt_irrefl _ hab
  have dac : a ≠ c := by intro h; subst h; exact lt_irrefl _ hac
  have dad : a ≠ d := by intro h; subst h; exact lt_irrefl _ had
  have dae : a ≠ e := by intro h; subst h; exact lt_irrefl _ hae
  have dbc : b ≠ c := by intro h; subst h; exact lt_irrefl _ hbc
  have dbd : b ≠ d := by intro h; subst h; exact lt_irrefl _ hbd
  have dbe : b ≠ e := by intro h; subst h; exact lt_irrefl _ hbe
  have dcd : c ≠ d := by intro h; subst h; exact lt_irrefl _ hcd
  have dce : c ≠ e := by intro h; subst h; exact lt_irrefl _ hce
  have dde : d ≠ e := by intro h; subst h; exact lt_irrefl _ hde
  have hag : ∀ w : Fin (k + 2), w ≠ P → w ≠ Q →
      σ w = (ntBeta (k + 2) j hjn) w := by
    intro w hwP hwQ
    rw [hσT, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hwP hwQ]
  by_cases hP : P ∈ ({a, b, c, d, e} : Finset (Fin (k + 2)))
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hP
    rcases hP with hPa | hPb | hPc | hPd | hPe
    · subst P
      by_cases hQ : Q ∈ ({b, c, d, e} : Finset (Fin (k + 2)))
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hQ
        rcases hQ with hQb | hQc | hQd | hQe
        · subst Q
          have e3 := hag c (Ne.symm dac) (Ne.symm dbc)
          have e4 := hag d (Ne.symm dad) (Ne.symm dbd)
          have e5 := hag e (Ne.symm dae) (Ne.symm dbe)
          have l1 : (ntBeta (k + 2) j hjn) c < (ntBeta (k + 2) j hjn) d := by
            rw [← e3, ← e4]; exact vcd
          have l2 : (ntBeta (k + 2) j hjn) d < (ntBeta (k + 2) j hjn) e := by
            rw [← e4, ← e5]; exact vde
          exact ntBeta_no123 hjn ⟨c, d, e, hcd, hde, l1, l2⟩
        · subst Q
          have e2 := hag b (Ne.symm dab) dbc
          have e4 := hag d (Ne.symm dad) (Ne.symm dcd)
          have e5 := hag e (Ne.symm dae) (Ne.symm dce)
          have l1 : (ntBeta (k + 2) j hjn) b < (ntBeta (k + 2) j hjn) d := by
            rw [← e2, ← e4]; exact lt_trans vbc vcd
          have l2 : (ntBeta (k + 2) j hjn) d < (ntBeta (k + 2) j hjn) e := by
            rw [← e4, ← e5]; exact vde
          exact ntBeta_no123 hjn ⟨b, d, e, hbd, hde, l1, l2⟩
        · subst Q
          have e2 := hag b (Ne.symm dab) dbd
          have e3 := hag c (Ne.symm dac) dcd
          have e5 := hag e (Ne.symm dae) (Ne.symm dde)
          have l1 : (ntBeta (k + 2) j hjn) b < (ntBeta (k + 2) j hjn) c := by
            rw [← e2, ← e3]; exact vbc
          have l2 : (ntBeta (k + 2) j hjn) c < (ntBeta (k + 2) j hjn) e := by
            rw [← e3, ← e5]; exact lt_trans vcd vde
          exact ntBeta_no123 hjn ⟨b, c, e, hbc, hce, l1, l2⟩
        · subst Q
          have e2 := hag b (Ne.symm dab) dbe
          have e3 := hag c (Ne.symm dac) dce
          have e4 := hag d (Ne.symm dad) dde
          have l1 : (ntBeta (k + 2) j hjn) b < (ntBeta (k + 2) j hjn) c := by
            rw [← e2, ← e3]; exact vbc
          have l2 : (ntBeta (k + 2) j hjn) c < (ntBeta (k + 2) j hjn) d := by
            rw [← e3, ← e4]; exact vcd
          exact ntBeta_no123 hjn ⟨b, c, d, hbc, hcd, l1, l2⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hQ
        obtain ⟨hQb, hQc, hQd, hQe⟩ := hQ
        have e2 := hag b (Ne.symm dab) (Ne.symm hQb)
        have e3 := hag c (Ne.symm dac) (Ne.symm hQc)
        have e4 := hag d (Ne.symm dad) (Ne.symm hQd)
        have l1 : (ntBeta (k + 2) j hjn) b < (ntBeta (k + 2) j hjn) c := by
          rw [← e2, ← e3]; exact vbc
        have l2 : (ntBeta (k + 2) j hjn) c < (ntBeta (k + 2) j hjn) d := by
          rw [← e3, ← e4]; exact vcd
        exact ntBeta_no123 hjn ⟨b, c, d, hbc, hcd, l1, l2⟩
    · subst P
      by_cases hQ : Q ∈ ({a, c, d, e} : Finset (Fin (k + 2)))
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hQ
        rcases hQ with hQa | hQc | hQd | hQe
        · subst Q
          have e3 := hag c (Ne.symm dbc) (Ne.symm dac)
          have e4 := hag d (Ne.symm dbd) (Ne.symm dad)
          have e5 := hag e (Ne.symm dbe) (Ne.symm dae)
          have l1 : (ntBeta (k + 2) j hjn) c < (ntBeta (k + 2) j hjn) d := by
            rw [← e3, ← e4]; exact vcd
          have l2 : (ntBeta (k + 2) j hjn) d < (ntBeta (k + 2) j hjn) e := by
            rw [← e4, ← e5]; exact vde
          exact ntBeta_no123 hjn ⟨c, d, e, hcd, hde, l1, l2⟩
        · subst Q
          have e1 := hag a dab dac
          have e4 := hag d (Ne.symm dbd) (Ne.symm dcd)
          have e5 := hag e (Ne.symm dbe) (Ne.symm dce)
          have l1 : (ntBeta (k + 2) j hjn) a < (ntBeta (k + 2) j hjn) d := by
            rw [← e1, ← e4]; exact lt_trans vab (lt_trans vbc vcd)
          have l2 : (ntBeta (k + 2) j hjn) d < (ntBeta (k + 2) j hjn) e := by
            rw [← e4, ← e5]; exact vde
          exact ntBeta_no123 hjn ⟨a, d, e, had, hde, l1, l2⟩
        · subst Q
          have e1 := hag a dab dad
          have e3 := hag c (Ne.symm dbc) dcd
          have e5 := hag e (Ne.symm dbe) (Ne.symm dde)
          have l1 : (ntBeta (k + 2) j hjn) a < (ntBeta (k + 2) j hjn) c := by
            rw [← e1, ← e3]; exact lt_trans vab vbc
          have l2 : (ntBeta (k + 2) j hjn) c < (ntBeta (k + 2) j hjn) e := by
            rw [← e3, ← e5]; exact lt_trans vcd vde
          exact ntBeta_no123 hjn ⟨a, c, e, hac, hce, l1, l2⟩
        · subst Q
          have e1 := hag a dab dae
          have e3 := hag c (Ne.symm dbc) dce
          have e4 := hag d (Ne.symm dbd) dde
          have l1 : (ntBeta (k + 2) j hjn) a < (ntBeta (k + 2) j hjn) c := by
            rw [← e1, ← e3]; exact lt_trans vab vbc
          have l2 : (ntBeta (k + 2) j hjn) c < (ntBeta (k + 2) j hjn) d := by
            rw [← e3, ← e4]; exact vcd
          exact ntBeta_no123 hjn ⟨a, c, d, hac, hcd, l1, l2⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hQ
        obtain ⟨hQa, hQc, hQd, hQe⟩ := hQ
        have e1 := hag a dab (Ne.symm hQa)
        have e3 := hag c (Ne.symm dbc) (Ne.symm hQc)
        have e4 := hag d (Ne.symm dbd) (Ne.symm hQd)
        have l1 : (ntBeta (k + 2) j hjn) a < (ntBeta (k + 2) j hjn) c := by
          rw [← e1, ← e3]; exact lt_trans vab vbc
        have l2 : (ntBeta (k + 2) j hjn) c < (ntBeta (k + 2) j hjn) d := by
          rw [← e3, ← e4]; exact vcd
        exact ntBeta_no123 hjn ⟨a, c, d, hac, hcd, l1, l2⟩
    · subst P
      by_cases hQ : Q ∈ ({a, b, d, e} : Finset (Fin (k + 2)))
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hQ
        rcases hQ with hQa | hQb | hQd | hQe
        · subst Q
          have e2 := hag b dbc (Ne.symm dab)
          have e4 := hag d (Ne.symm dcd) (Ne.symm dad)
          have e5 := hag e (Ne.symm dce) (Ne.symm dae)
          have l1 : (ntBeta (k + 2) j hjn) b < (ntBeta (k + 2) j hjn) d := by
            rw [← e2, ← e4]; exact lt_trans vbc vcd
          have l2 : (ntBeta (k + 2) j hjn) d < (ntBeta (k + 2) j hjn) e := by
            rw [← e4, ← e5]; exact vde
          exact ntBeta_no123 hjn ⟨b, d, e, hbd, hde, l1, l2⟩
        · subst Q
          have e1 := hag a dac dab
          have e4 := hag d (Ne.symm dcd) (Ne.symm dbd)
          have e5 := hag e (Ne.symm dce) (Ne.symm dbe)
          have l1 : (ntBeta (k + 2) j hjn) a < (ntBeta (k + 2) j hjn) d := by
            rw [← e1, ← e4]; exact lt_trans vab (lt_trans vbc vcd)
          have l2 : (ntBeta (k + 2) j hjn) d < (ntBeta (k + 2) j hjn) e := by
            rw [← e4, ← e5]; exact vde
          exact ntBeta_no123 hjn ⟨a, d, e, had, hde, l1, l2⟩
        · subst Q
          have e1 := hag a dac dad
          have e2 := hag b dbc dbd
          have e5 := hag e (Ne.symm dce) (Ne.symm dde)
          have l1 : (ntBeta (k + 2) j hjn) a < (ntBeta (k + 2) j hjn) b := by
            rw [← e1, ← e2]; exact vab
          have l2 : (ntBeta (k + 2) j hjn) b < (ntBeta (k + 2) j hjn) e := by
            rw [← e2, ← e5]; exact lt_trans vbc (lt_trans vcd vde)
          exact ntBeta_no123 hjn ⟨a, b, e, hab, hbe, l1, l2⟩
        · subst Q
          have e1 := hag a dac dae
          have e2 := hag b dbc dbe
          have e4 := hag d (Ne.symm dcd) dde
          have l1 : (ntBeta (k + 2) j hjn) a < (ntBeta (k + 2) j hjn) b := by
            rw [← e1, ← e2]; exact vab
          have l2 : (ntBeta (k + 2) j hjn) b < (ntBeta (k + 2) j hjn) d := by
            rw [← e2, ← e4]; exact lt_trans vbc vcd
          exact ntBeta_no123 hjn ⟨a, b, d, hab, hbd, l1, l2⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hQ
        obtain ⟨hQa, hQb, hQd, hQe⟩ := hQ
        have e1 := hag a dac (Ne.symm hQa)
        have e2 := hag b dbc (Ne.symm hQb)
        have e4 := hag d (Ne.symm dcd) (Ne.symm hQd)
        have l1 : (ntBeta (k + 2) j hjn) a < (ntBeta (k + 2) j hjn) b := by
          rw [← e1, ← e2]; exact vab
        have l2 : (ntBeta (k + 2) j hjn) b < (ntBeta (k + 2) j hjn) d := by
          rw [← e2, ← e4]; exact lt_trans vbc vcd
        exact ntBeta_no123 hjn ⟨a, b, d, hab, hbd, l1, l2⟩
    · subst P
      by_cases hQ : Q ∈ ({a, b, c, e} : Finset (Fin (k + 2)))
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hQ
        rcases hQ with hQa | hQb | hQc | hQe
        · subst Q
          have e2 := hag b dbd (Ne.symm dab)
          have e3 := hag c dcd (Ne.symm dac)
          have e5 := hag e (Ne.symm dde) (Ne.symm dae)
          have l1 : (ntBeta (k + 2) j hjn) b < (ntBeta (k + 2) j hjn) c := by
            rw [← e2, ← e3]; exact vbc
          have l2 : (ntBeta (k + 2) j hjn) c < (ntBeta (k + 2) j hjn) e := by
            rw [← e3, ← e5]; exact lt_trans vcd vde
          exact ntBeta_no123 hjn ⟨b, c, e, hbc, hce, l1, l2⟩
        · subst Q
          have e1 := hag a dad dab
          have e3 := hag c dcd (Ne.symm dbc)
          have e5 := hag e (Ne.symm dde) (Ne.symm dbe)
          have l1 : (ntBeta (k + 2) j hjn) a < (ntBeta (k + 2) j hjn) c := by
            rw [← e1, ← e3]; exact lt_trans vab vbc
          have l2 : (ntBeta (k + 2) j hjn) c < (ntBeta (k + 2) j hjn) e := by
            rw [← e3, ← e5]; exact lt_trans vcd vde
          exact ntBeta_no123 hjn ⟨a, c, e, hac, hce, l1, l2⟩
        · subst Q
          have e1 := hag a dad dac
          have e2 := hag b dbd dbc
          have e5 := hag e (Ne.symm dde) (Ne.symm dce)
          have l1 : (ntBeta (k + 2) j hjn) a < (ntBeta (k + 2) j hjn) b := by
            rw [← e1, ← e2]; exact vab
          have l2 : (ntBeta (k + 2) j hjn) b < (ntBeta (k + 2) j hjn) e := by
            rw [← e2, ← e5]; exact lt_trans vbc (lt_trans vcd vde)
          exact ntBeta_no123 hjn ⟨a, b, e, hab, hbe, l1, l2⟩
        · subst Q
          have e1 := hag a dad dae
          have e2 := hag b dbd dbe
          have e3 := hag c dcd dce
          have l1 : (ntBeta (k + 2) j hjn) a < (ntBeta (k + 2) j hjn) b := by
            rw [← e1, ← e2]; exact vab
          have l2 : (ntBeta (k + 2) j hjn) b < (ntBeta (k + 2) j hjn) c := by
            rw [← e2, ← e3]; exact vbc
          exact ntBeta_no123 hjn ⟨a, b, c, hab, hbc, l1, l2⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hQ
        obtain ⟨hQa, hQb, hQc, hQe⟩ := hQ
        have e1 := hag a dad (Ne.symm hQa)
        have e2 := hag b dbd (Ne.symm hQb)
        have e3 := hag c dcd (Ne.symm hQc)
        have l1 : (ntBeta (k + 2) j hjn) a < (ntBeta (k + 2) j hjn) b := by
          rw [← e1, ← e2]; exact vab
        have l2 : (ntBeta (k + 2) j hjn) b < (ntBeta (k + 2) j hjn) c := by
          rw [← e2, ← e3]; exact vbc
        exact ntBeta_no123 hjn ⟨a, b, c, hab, hbc, l1, l2⟩
    · subst P
      by_cases hQ : Q ∈ ({a, b, c, d} : Finset (Fin (k + 2)))
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hQ
        rcases hQ with hQa | hQb | hQc | hQd
        · subst Q
          have e2 := hag b dbe (Ne.symm dab)
          have e3 := hag c dce (Ne.symm dac)
          have e4 := hag d dde (Ne.symm dad)
          have l1 : (ntBeta (k + 2) j hjn) b < (ntBeta (k + 2) j hjn) c := by
            rw [← e2, ← e3]; exact vbc
          have l2 : (ntBeta (k + 2) j hjn) c < (ntBeta (k + 2) j hjn) d := by
            rw [← e3, ← e4]; exact vcd
          exact ntBeta_no123 hjn ⟨b, c, d, hbc, hcd, l1, l2⟩
        · subst Q
          have e1 := hag a dae dab
          have e3 := hag c dce (Ne.symm dbc)
          have e4 := hag d dde (Ne.symm dbd)
          have l1 : (ntBeta (k + 2) j hjn) a < (ntBeta (k + 2) j hjn) c := by
            rw [← e1, ← e3]; exact lt_trans vab vbc
          have l2 : (ntBeta (k + 2) j hjn) c < (ntBeta (k + 2) j hjn) d := by
            rw [← e3, ← e4]; exact vcd
          exact ntBeta_no123 hjn ⟨a, c, d, hac, hcd, l1, l2⟩
        · subst Q
          have e1 := hag a dae dac
          have e2 := hag b dbe dbc
          have e4 := hag d dde (Ne.symm dcd)
          have l1 : (ntBeta (k + 2) j hjn) a < (ntBeta (k + 2) j hjn) b := by
            rw [← e1, ← e2]; exact vab
          have l2 : (ntBeta (k + 2) j hjn) b < (ntBeta (k + 2) j hjn) d := by
            rw [← e2, ← e4]; exact lt_trans vbc vcd
          exact ntBeta_no123 hjn ⟨a, b, d, hab, hbd, l1, l2⟩
        · subst Q
          have e1 := hag a dae dad
          have e2 := hag b dbe dbd
          have e3 := hag c dce dcd
          have l1 : (ntBeta (k + 2) j hjn) a < (ntBeta (k + 2) j hjn) b := by
            rw [← e1, ← e2]; exact vab
          have l2 : (ntBeta (k + 2) j hjn) b < (ntBeta (k + 2) j hjn) c := by
            rw [← e2, ← e3]; exact vbc
          exact ntBeta_no123 hjn ⟨a, b, c, hab, hbc, l1, l2⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hQ
        obtain ⟨hQa, hQb, hQc, hQd⟩ := hQ
        have e1 := hag a dae (Ne.symm hQa)
        have e2 := hag b dbe (Ne.symm hQb)
        have e3 := hag c dce (Ne.symm hQc)
        have l1 : (ntBeta (k + 2) j hjn) a < (ntBeta (k + 2) j hjn) b := by
          rw [← e1, ← e2]; exact vab
        have l2 : (ntBeta (k + 2) j hjn) b < (ntBeta (k + 2) j hjn) c := by
          rw [← e2, ← e3]; exact vbc
        exact ntBeta_no123 hjn ⟨a, b, c, hab, hbc, l1, l2⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hP
    obtain ⟨hPa, hPb, hPc, hPd, hPe⟩ := hP
    by_cases hQ : Q ∈ ({a, b, c, d, e} : Finset (Fin (k + 2)))
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hQ
      rcases hQ with hQa | hQb | hQc | hQd | hQe
      · subst Q
        have e2 := hag b (Ne.symm hPb) (Ne.symm dab)
        have e3 := hag c (Ne.symm hPc) (Ne.symm dac)
        have e4 := hag d (Ne.symm hPd) (Ne.symm dad)
        have l1 : (ntBeta (k + 2) j hjn) b < (ntBeta (k + 2) j hjn) c := by
          rw [← e2, ← e3]; exact vbc
        have l2 : (ntBeta (k + 2) j hjn) c < (ntBeta (k + 2) j hjn) d := by
          rw [← e3, ← e4]; exact vcd
        exact ntBeta_no123 hjn ⟨b, c, d, hbc, hcd, l1, l2⟩
      · subst Q
        have e1 := hag a (Ne.symm hPa) dab
        have e3 := hag c (Ne.symm hPc) (Ne.symm dbc)
        have e4 := hag d (Ne.symm hPd) (Ne.symm dbd)
        have l1 : (ntBeta (k + 2) j hjn) a < (ntBeta (k + 2) j hjn) c := by
          rw [← e1, ← e3]; exact lt_trans vab vbc
        have l2 : (ntBeta (k + 2) j hjn) c < (ntBeta (k + 2) j hjn) d := by
          rw [← e3, ← e4]; exact vcd
        exact ntBeta_no123 hjn ⟨a, c, d, hac, hcd, l1, l2⟩
      · subst Q
        have e1 := hag a (Ne.symm hPa) dac
        have e2 := hag b (Ne.symm hPb) dbc
        have e4 := hag d (Ne.symm hPd) (Ne.symm dcd)
        have l1 : (ntBeta (k + 2) j hjn) a < (ntBeta (k + 2) j hjn) b := by
          rw [← e1, ← e2]; exact vab
        have l2 : (ntBeta (k + 2) j hjn) b < (ntBeta (k + 2) j hjn) d := by
          rw [← e2, ← e4]; exact lt_trans vbc vcd
        exact ntBeta_no123 hjn ⟨a, b, d, hab, hbd, l1, l2⟩
      · subst Q
        have e1 := hag a (Ne.symm hPa) dad
        have e2 := hag b (Ne.symm hPb) dbd
        have e3 := hag c (Ne.symm hPc) dcd
        have l1 : (ntBeta (k + 2) j hjn) a < (ntBeta (k + 2) j hjn) b := by
          rw [← e1, ← e2]; exact vab
        have l2 : (ntBeta (k + 2) j hjn) b < (ntBeta (k + 2) j hjn) c := by
          rw [← e2, ← e3]; exact vbc
        exact ntBeta_no123 hjn ⟨a, b, c, hab, hbc, l1, l2⟩
      · subst Q
        have e1 := hag a (Ne.symm hPa) dae
        have e2 := hag b (Ne.symm hPb) dbe
        have e3 := hag c (Ne.symm hPc) dce
        have l1 : (ntBeta (k + 2) j hjn) a < (ntBeta (k + 2) j hjn) b := by
          rw [← e1, ← e2]; exact vab
        have l2 : (ntBeta (k + 2) j hjn) b < (ntBeta (k + 2) j hjn) c := by
          rw [← e2, ← e3]; exact vbc
        exact ntBeta_no123 hjn ⟨a, b, c, hab, hbc, l1, l2⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hQ
      obtain ⟨hQa, hQb, hQc, hQd, hQe⟩ := hQ
      have e1 := hag a (Ne.symm hPa) (Ne.symm hQa)
      have e2 := hag b (Ne.symm hPb) (Ne.symm hQb)
      have e3 := hag c (Ne.symm hPc) (Ne.symm hQc)
      have l1 : (ntBeta (k + 2) j hjn) a < (ntBeta (k + 2) j hjn) b := by
        rw [← e1, ← e2]; exact vab
      have l2 : (ntBeta (k + 2) j hjn) b < (ntBeta (k + 2) j hjn) c := by
        rw [← e2, ← e3]; exact vbc
      exact ntBeta_no123 hjn ⟨a, b, c, hab, hbc, l1, l2⟩

/-- The `j = 0` swap family has no patterns: `beta_0` is the full reversal. -/
private lemma ntK_zero_empty {n : ℕ} (hj : 0 + 1 ≤ n) :
    ntK n 0 hj = ∅ := by
  have hbetaLT : ∀ a b : Fin n,
      (ntBeta n 0 hj a < ntBeta n 0 hj b) ↔ (b.val < a.val) := by
    intro a b
    rw [Fin.lt_def, ntBeta_val hj, ntBeta_val hj]
    have ha := a.is_lt
    have hb := b.is_lt
    simp only [Nat.not_lt_zero, ite_false]
    omega
  rw [Set.eq_empty_iff_forall_notMem]
  intro z hz
  obtain ⟨⟨P, Q, hPQ, hκ⟩, hpat⟩ := hz
  rcases hpat with ⟨i1, i2, i3, i4, h12, h23, h34, g12, g23, g34⟩ |
    ⟨i1, i2, i3, i4, h12, h23, h34, g31, g42, g13⟩
  · have hocc := ntBeta_occur hj hPQ hκ h12 h23 h34 (Or.inl ⟨g12, g23, g34⟩)
    have d12 : i1 ≠ i2 := Fin.ne_of_val_ne (by omega)
    have d13 : i1 ≠ i3 := Fin.ne_of_val_ne (by omega)
    have d14 : i1 ≠ i4 := Fin.ne_of_val_ne (by omega)
    have d23 : i2 ≠ i3 := Fin.ne_of_val_ne (by omega)
    have d24 : i2 ≠ i4 := Fin.ne_of_val_ne (by omega)
    have d34 : i3 ≠ i4 := Fin.ne_of_val_ne (by omega)
    have h14 : i1.val < i4.val := lt_trans h12 (lt_trans h23 h34)
    rcases hocc with ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩
    · rw [hP, hQ] at hκ
      have e3 : z i3 = ntBeta n 0 hj i1 := by
        rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_right]
      have e4 : z i4 = ntBeta n 0 hj i4 := by
        rw [hκ, Equiv.Perm.mul_apply,
          Equiv.swap_apply_of_ne_of_ne d14.symm d34.symm]
      have g34' : i4.val < i1.val := (hbetaLT _ _).mp (by rw [← e3, ← e4]; exact g34)
      omega
    · rw [hP, hQ] at hκ
      have e3 : z i3 = ntBeta n 0 hj i1 := by
        rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
      have e4 : z i4 = ntBeta n 0 hj i4 := by
        rw [hκ, Equiv.Perm.mul_apply,
          Equiv.swap_apply_of_ne_of_ne d34.symm d14.symm]
      have g34' : i4.val < i1.val := (hbetaLT _ _).mp (by rw [← e3, ← e4]; exact g34)
      omega
    · rw [hP, hQ] at hκ
      have e1 : z i1 = ntBeta n 0 hj i1 := by
        rw [hκ, Equiv.Perm.mul_apply,
          Equiv.swap_apply_of_ne_of_ne d12 d14]
      have e2 : z i2 = ntBeta n 0 hj i4 := by
        rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
      have g12' : i4.val < i1.val := (hbetaLT _ _).mp (by rw [← e1, ← e2]; exact g12)
      omega
    · rw [hP, hQ] at hκ
      have e1 : z i1 = ntBeta n 0 hj i1 := by
        rw [hκ, Equiv.Perm.mul_apply,
          Equiv.swap_apply_of_ne_of_ne d14 d12]
      have e2 : z i2 = ntBeta n 0 hj i4 := by
        rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_right]
      have g12' : i4.val < i1.val := (hbetaLT _ _).mp (by rw [← e1, ← e2]; exact g12)
      omega
  · have hocc := ntBeta_occur hj hPQ hκ h12 h23 h34 (Or.inr ⟨g31, g42, g13⟩)
    have d12 : i1 ≠ i2 := Fin.ne_of_val_ne (by omega)
    have d13 : i1 ≠ i3 := Fin.ne_of_val_ne (by omega)
    have d14 : i1 ≠ i4 := Fin.ne_of_val_ne (by omega)
    have d23 : i2 ≠ i3 := Fin.ne_of_val_ne (by omega)
    have d24 : i2 ≠ i4 := Fin.ne_of_val_ne (by omega)
    have d34 : i3 ≠ i4 := Fin.ne_of_val_ne (by omega)
    have h14 : i1.val < i4.val := lt_trans h12 (lt_trans h23 h34)
    rcases hocc with ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩ | ⟨hP, hQ⟩
    · rw [hP, hQ] at hκ
      have e3 : z i3 = ntBeta n 0 hj i1 := by
        rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_right]
      have e4 : z i4 = ntBeta n 0 hj i4 := by
        rw [hκ, Equiv.Perm.mul_apply,
          Equiv.swap_apply_of_ne_of_ne d14.symm d34.symm]
      have g31' : i4.val < i1.val := (hbetaLT _ _).mp (by rw [← e3, ← e4]; exact g31)
      omega
    · rw [hP, hQ] at hκ
      have e3 : z i3 = ntBeta n 0 hj i1 := by
        rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
      have e4 : z i4 = ntBeta n 0 hj i4 := by
        rw [hκ, Equiv.Perm.mul_apply,
          Equiv.swap_apply_of_ne_of_ne d34.symm d14.symm]
      have g31' : i4.val < i1.val := (hbetaLT _ _).mp (by rw [← e3, ← e4]; exact g31)
      omega
    · rw [hP, hQ] at hκ
      have e1 : z i1 = ntBeta n 0 hj i1 := by
        rw [hκ, Equiv.Perm.mul_apply,
          Equiv.swap_apply_of_ne_of_ne d12 d14]
      have e2 : z i2 = ntBeta n 0 hj i4 := by
        rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
      have g13' : i4.val < i1.val := (hbetaLT _ _).mp (by rw [← e1, ← e2]; exact g13)
      omega
    · rw [hP, hQ] at hκ
      have e1 : z i1 = ntBeta n 0 hj i1 := by
        rw [hκ, Equiv.Perm.mul_apply,
          Equiv.swap_apply_of_ne_of_ne d14 d12]
      have e2 : z i2 = ntBeta n 0 hj i4 := by
        rw [hκ, Equiv.Perm.mul_apply, Equiv.swap_apply_right]
      have g13' : i4.val < i1.val := (hbetaLT _ _).mp (by rw [← e1, ← e2]; exact g13)
      omega

/-- Generic elements from `inc5`: packaging `E`, pattern and non-`K` facts. -/
private lemma ntMemG_of_inc5 {m : ℕ} (hm : 5 ≤ m) {σ : Equiv.Perm (Fin (m + 2))}
    (hE : σ ∈ ntE (m + 1)) (hinc : ntInc5 (m + 2) σ) : σ ∈ ntG (m + 1) := by
  refine ⟨hE, ntInc5_pat hinc, ?_⟩
  intro j hj hmem
  by_cases hj0 : j = 0
  · subst hj0
    rw [ntK_zero_empty hj] at hmem
    exact absurd hmem (Set.notMem_empty _)
  · obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
    exact ntInc5_notK (by omega) (by omega) hj hinc hmem

/-- The even reference permutation is generic. -/
private lemma ntEven_memG {m : ℕ} (hm : 5 ≤ m) : ntEven (m + 2) ∈ ntG (m + 1) := by
  have hid : ∀ x : Fin (m + 2), ntEven (m + 2) x = x := fun x => rfl
  have h01 : (0 : Fin (m + 2)) ≠ Fin.last (m + 1) := by
    intro hcon
    have hvv := congrArg Fin.val hcon
    simp only [Fin.val_zero, Fin.val_last] at hvv
    omega
  have hE : ntEven (m + 2) ∈ ntE (m + 1) := by
    constructor
    · change (1 : Equiv.Perm (Fin (m + 2))) 0 ≠ Fin.last (m + 1)
      exact h01
    · change (1 : Equiv.Perm (Fin (m + 2))) (Fin.last (m + 1)) ≠ 0
      exact fun h => h01 h.symm
  have hpat : ntPat (m + 2) (ntEven (m + 2)) := by
    refine Or.inl ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩,
      by simp, by simp, by simp, ?_, ?_, ?_⟩
    · simp only [hid, Fin.lt_def]; omega
    · simp only [hid, Fin.lt_def]; omega
    · simp only [hid, Fin.lt_def]; omega
  have hinc : ntInc5 (m + 2) (ntEven (m + 2)) := by
    refine ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩,
      ⟨4, by omega⟩, by simp, by simp, by simp, by simp, ?_, ?_, ?_, ?_⟩
    · simp only [hid, Fin.lt_def]; omega
    · simp only [hid, Fin.lt_def]; omega
    · simp only [hid, Fin.lt_def]; omega
    · simp only [hid, Fin.lt_def]; omega
  exact ntMemG_of_inc5 hm hE hinc

/-- The odd reference permutation is generic. -/
private lemma ntOdd_memG {m : ℕ} (hm : 5 ≤ m) : ntOdd m ∈ ntG (m + 1) := by
  have hfix : ∀ x : Fin (m + 2), x.val ≤ 4 → ntOdd m x = x := by
    intro x hx
    unfold ntOdd
    apply Equiv.swap_apply_of_ne_of_ne
    · intro hcon
      have hv : x.val = m := congrArg Fin.val hcon
      omega
    · intro hcon
      have hv : x.val = m + 1 := congrArg Fin.val hcon
      omega
  have hlast : Fin.last (m + 1) = (⟨m + 1, by omega⟩ : Fin (m + 2)) :=
    Fin.ext (Fin.val_last _)
  have h01 : (0 : Fin (m + 2)) ≠ Fin.last (m + 1) := by
    intro hcon
    have hvv := congrArg Fin.val hcon
    simp only [Fin.val_zero, Fin.val_last] at hvv
    omega
  have hE : ntOdd m ∈ ntE (m + 1) := by
    constructor
    · have e0 : ntOdd m 0 = 0 := hfix 0 (by rw [Fin.val_zero]; omega)
      rw [e0]
      intro hcon
      have hvv := congrArg Fin.val hcon
      simp only [Fin.val_zero, Fin.val_last] at hvv
      omega
    · rw [hlast]
      intro hcon
      have e : ntOdd m (⟨m + 1, by omega⟩ : Fin (m + 2)) =
          (⟨m, by omega⟩ : Fin (m + 2)) := Equiv.swap_apply_right _ _
      have h2 : (⟨m, by omega⟩ : Fin (m + 2)) = 0 := e.symm.trans hcon
      have hmv : m = 0 := congrArg Fin.val h2
      omega
  have hpat : ntPat (m + 2) (ntOdd m) := by
    refine Or.inl ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩,
      by simp, by simp, by simp, ?_, ?_, ?_⟩
    · rw [hfix _ (by simp), hfix _ (by simp), Fin.lt_def]; simp
    · rw [hfix _ (by simp), hfix _ (by simp), Fin.lt_def]; simp
    · rw [hfix _ (by simp), hfix _ (by simp), Fin.lt_def]; simp
  have hinc : ntInc5 (m + 2) (ntOdd m) := by
    refine ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩,
      ⟨4, by omega⟩, by simp, by simp, by simp, by simp, ?_, ?_, ?_, ?_⟩
    · rw [hfix _ (by simp), hfix _ (by simp), Fin.lt_def]; simp
    · rw [hfix _ (by simp), hfix _ (by simp), Fin.lt_def]; simp
    · rw [hfix _ (by simp), hfix _ (by simp), Fin.lt_def]; simp
    · rw [hfix _ (by simp), hfix _ (by simp), Fin.lt_def]; simp
  exact ntMemG_of_inc5 hm hE hinc

/-- Insertions into the identity at non-inert positions are generic. -/
private lemma ntG_id_ins {m : ℕ} (hm : 5 ≤ m) (y' v' : Fin (m + 2))
    (hne : (y' ≠ 0 ∨ v' ≠ Fin.last (m + 1)) ∧
      (y' ≠ Fin.last (m + 1) ∨ v' ≠ 0)) :
    ntIns y' v' 1 ∈ ntG (m + 1) :=
  ntMemG_of_inc5 hm (ntIns_memE y' v' 1 rfl hne) (ntInc5_id_ins hm y' v')

/-- Insertions into the `2-3` swap at non-inert positions are generic. -/
private lemma ntG_swap23_ins {m : ℕ} (hm : 5 ≤ m) (y' v' : Fin (m + 2))
    (μ : Equiv.Perm (Fin (m + 1)))
    (hμ : μ = Equiv.swap (⟨2, by omega⟩ : Fin (m + 1)) ⟨3, by omega⟩)
    (hne : (y' ≠ 0 ∨ v' ≠ Fin.last (m + 1)) ∧
      (y' ≠ Fin.last (m + 1) ∨ v' ≠ 0)) :
    ntIns y' v' μ ∈ ntG (m + 1) := by
  have hμ0 : μ 0 = 0 := by
    rw [hμ]
    exact ntSwap_fix_vals _ _ _ (by simp) (by simp)
  exact ntMemG_of_inc5 hm (ntIns_memE _ _ _ hμ0 hne)
    (ntInc5_swap23_ins hm y' v' μ hμ)

/-- Branch 1: insertions at positive positions land in a reference class. -/
private lemma ntIns_branch1 {m : ℕ} (hm : 5 ≤ m)
    (hIH : ∀ ρ ∈ ntG (m + 1),
      Relation.EqvGen (ntMove (m + 2)) ρ (ntEven (m + 2)) ∨
        Relation.EqvGen (ntMove (m + 2)) ρ (ntOdd m))
    {y v : Fin (m + 3)} {ρ : Equiv.Perm (Fin (m + 2))}
    (hρ : ρ ∈ ntG (m + 1))
    (hy1 : 1 ≤ y.val) (hv1 : 1 ≤ v.val)
    (hne1 : (y.val, v.val) ≠ (1, m + 2)) (hne2 : (y.val, v.val) ≠ (m + 2, 1)) :
    Relation.EqvGen (ntMove (m + 3)) (ntIns y v ρ) (ntEven (m + 3)) ∨
      Relation.EqvGen (ntMove (m + 3)) (ntIns y v ρ) (ntOdd (m + 1)) := by
  have hy'lt : y.val < m + 3 := y.is_lt
  have hv'lt : v.val < m + 3 := v.is_lt
  set y' : Fin (m + 2) := ⟨y.val - 1, by omega⟩ with hy'def
  set v' : Fin (m + 2) := ⟨v.val - 1, by omega⟩ with hv'def
  have ey : y'.val = y.val - 1 := rfl
  have ev : v'.val = v.val - 1 := rfl
  have hy : y = y'.succ := by
    apply Fin.ext
    rw [Fin.val_succ]
    omega
  have hv : v = v'.succ := by
    apply Fin.ext
    rw [Fin.val_succ]
    omega
  have hne' : (y' ≠ 0 ∨ v' ≠ Fin.last (m + 1)) ∧
      (y' ≠ Fin.last (m + 1) ∨ v' ≠ 0) := by
    constructor
    · by_contra hc
      simp only [not_or, not_not] at hc
      obtain ⟨hy0, hv0⟩ := hc
      have h1 : y'.val = 0 := by rw [hy0]; exact Fin.val_zero _
      have h2 : v'.val = m + 1 := by rw [hv0]; exact Fin.val_last _
      have hyv : y.val = 1 := by omega
      have hvv : v.val = m + 2 := by omega
      exact hne1 (by rw [hyv, hvv])
    · by_contra hc
      simp only [not_or, not_not] at hc
      obtain ⟨hy0, hv0⟩ := hc
      have h1 : y'.val = m + 1 := by rw [hy0]; exact Fin.val_last _
      have h2 : v'.val = 0 := by rw [hv0]; exact Fin.val_zero _
      have hyv : y.val = m + 2 := by omega
      have hvv : v.val = 1 := by omega
      exact hne2 (by rw [hyv, hvv])
  rcases hIH ρ hρ with hρe | hρo
  · have hμ'G : ntEven (m + 2) ∈ ntG (m + 1) := ntEven_memG hm
    have hρμ : Relation.EqvGen (ntMove (m + 2)) ρ (ntEven (m + 2)) :=
      ntG_sameSign hIH hρ hμ'G (ntEqvGen_sign hρe)
    have hcongr : Relation.EqvGen (ntMove (m + 3)) (ntIns y v ρ)
        (ntIns y v (ntEven (m + 2))) := ntEqvGen_ins y v hρμ
    have hEven0 : ntEven (m + 2) = ntIns 0 (0 : Fin (m + 2)) 1 := by
      have e : ntIns (0 : Fin (m + 2)) 0 (1 : Equiv.Perm (Fin (m + 1))) = 1 :=
        ntIns_zero_one
      rw [e]
      rfl
    rw [hEven0, ntIns_comm_zero y v 1 y' v' hy hv] at hcongr
    have hinnerG : ntIns y' v' (1 : Equiv.Perm (Fin (m + 1))) ∈ ntG (m + 1) :=
      ntG_id_ins hm y' v' hne'
    rcases hIH _ hinnerG with hI | hI
    · exact ntIns_close_even hcongr hI
    · exact ntIns_close_odd hcongr hI
  · have hμ'oddG : ntIns (0 : Fin (m + 2)) 0
        (Equiv.swap (⟨2, by omega⟩ : Fin (m + 1)) ⟨3, by omega⟩) ∈
        ntG (m + 1) := by
      have h01 : (0 : Fin (m + 2)) ≠ Fin.last (m + 1) := by
        intro hcon
        have hvv := congrArg Fin.val hcon
        simp only [Fin.val_zero, Fin.val_last] at hvv
        omega
      have hne0 : ((0 : Fin (m + 2)) ≠ 0 ∨ (0 : Fin (m + 2)) ≠ Fin.last (m + 1)) ∧
          ((0 : Fin (m + 2)) ≠ Fin.last (m + 1) ∨ (0 : Fin (m + 2)) ≠ 0) :=
        ⟨Or.inr h01, Or.inl h01⟩
      exact ntG_swap23_ins hm 0 0 _ rfl hne0
    have hsign' : Equiv.Perm.sign (ntIns (0 : Fin (m + 2)) 0
        (Equiv.swap (⟨2, by omega⟩ : Fin (m + 1)) ⟨3, by omega⟩)) = -1 := by
      have e : ntIns (0 : Fin (m + 2)) 0
          (Equiv.swap (⟨2, by omega⟩ : Fin (m + 1)) ⟨3, by omega⟩) =
          Equiv.swap (⟨3, by omega⟩ : Fin (m + 2)) ⟨4, by omega⟩ := by
        rw [ntIns_zero_swap]
        congr 1
      rw [e]
      apply Equiv.Perm.sign_swap
      intro hcon
      have e2 : (3 : ℕ) = 4 := congrArg Fin.val hcon
      omega
    have hρo_sign : Equiv.Perm.sign ρ = -1 := by
      have e1 := ntEqvGen_sign hρo
      have e2 : Equiv.Perm.sign (ntOdd m) = -1 := by
        unfold ntOdd
        apply Equiv.Perm.sign_swap
        intro hcon
        have e3 : m = m + 1 := congrArg Fin.val hcon
        omega
      rw [e2] at e1
      exact e1
    have hρμ := ntG_sameSign hIH hρ hμ'oddG (hρo_sign.trans hsign'.symm)
    have hcongr := ntEqvGen_ins y v hρμ
    rw [ntIns_comm_zero y v _ y' v' hy hv] at hcongr
    have hinnerG := ntG_swap23_ins hm y' v' _ rfl hne'
    rcases hIH _ hinnerG with hI | hI
    · exact ntIns_close_even hcongr hI
    · exact ntIns_close_odd hcongr hI

/-- Closing a `last`-insertion chain at the odd reference (extra step). -/
private lemma ntIns_closeLast_odd {m : ℕ} (hm : 5 ≤ m)
    (hIH : ∀ ρ ∈ ntG (m + 1),
      Relation.EqvGen (ntMove (m + 2)) ρ (ntEven (m + 2)) ∨
        Relation.EqvGen (ntMove (m + 2)) ρ (ntOdd m))
    {w : Equiv.Perm (Fin (m + 3))}
    (hcongr : Relation.EqvGen (ntMove (m + 3)) w
      (ntIns (Fin.last (m + 2)) (Fin.last (m + 2)) (ntOdd m))) :
    Relation.EqvGen (ntMove (m + 3)) w (ntEven (m + 3)) ∨
      Relation.EqvGen (ntMove (m + 3)) w (ntOdd (m + 1)) := by
  have e1 : ntOdd m =
      Equiv.swap (⟨m, by omega⟩ : Fin (m + 2)) ⟨m + 1, by omega⟩ := rfl
  have hS : ntIns (Fin.last (m + 2)) (Fin.last (m + 2)) (ntOdd m) =
      Equiv.swap ((⟨m, by omega⟩ : Fin (m + 2))).castSucc
        ((⟨m + 1, by omega⟩ : Fin (m + 2))).castSucc := by
    rw [e1]
    exact ntIns_last_swap _ _
  have h01 : (0 : Fin (m + 3)) ≠ Fin.last (m + 2) := by
    intro hcon
    have hvv := congrArg Fin.val hcon
    simp only [Fin.val_zero, Fin.val_last] at hvv
    omega
  have hS0 : ntIns (Fin.last (m + 2)) (Fin.last (m + 2)) (ntOdd m) 0 = 0 := by
    rw [hS]
    exact ntSwap_fix_vals _ _ _
      (by change (0 : ℕ) ≠ m; omega) (by change (0 : ℕ) ≠ m + 1; omega)
  obtain ⟨s', hs'⟩ := ntIns_exists _ _ _ hS0
  have hs'swap : s' =
      Equiv.swap (⟨m - 1, by omega⟩ : Fin (m + 2)) ⟨m, by omega⟩ := by
    apply ntIns_injective (0 : Fin (m + 3)) (0 : Fin (m + 3))
    rw [← hs', hS]
    apply Equiv.Perm.ext
    intro x
    by_cases hx0 : x = 0
    · subst hx0
      rw [ntIns_apply_same]
      exact ntSwap_fix_vals _ _ _
        (by change (0 : ℕ) ≠ m; omega) (by change (0 : ℕ) ≠ m + 1; omega)
    · obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq hx0
      rw [← hi, ntIns_apply_succAbove, Fin.succAbove_zero_apply,
        Fin.succAbove_zero_apply]
      by_cases hA : i.succ = ((⟨m, by omega⟩ : Fin (m + 2))).castSucc
      · have hvv := congrArg Fin.val hA
        rw [Fin.val_succ] at hvv
        have hiv : i.val + 1 = m := hvv
        have hi_eq : i = (⟨m - 1, by omega⟩ : Fin (m + 2)) :=
          Fin.ext (by change i.val = m - 1; omega)
        rw [hA, Equiv.swap_apply_left, hi_eq, Equiv.swap_apply_left]
        rfl
      · by_cases hB : i.succ = ((⟨m + 1, by omega⟩ : Fin (m + 2))).castSucc
        · have hvv := congrArg Fin.val hB
          rw [Fin.val_succ] at hvv
          have hiv : i.val + 1 = m + 1 := hvv
          have hi_eq : i = (⟨m, by omega⟩ : Fin (m + 2)) :=
            Fin.ext (by change i.val = m; omega)
          rw [hB, Equiv.swap_apply_right, hi_eq, Equiv.swap_apply_right]
          apply Fin.ext
          rw [Fin.val_castSucc, Fin.val_succ]
          change m = m - 1 + 1
          omega
        · have eL : Equiv.swap _ _ (i.succ) = i.succ :=
            Equiv.swap_apply_of_ne_of_ne hA hB
          have eR :
              (Equiv.swap (⟨m - 1, by omega⟩ : Fin (m + 2)) ⟨m, by omega⟩)
                i = i := by
            apply ntSwap_fix_vals
            · intro hcon
              have hiv : i.val = m - 1 := hcon
              have hAs : i.succ =
                  ((⟨m, by omega⟩ : Fin (m + 2))).castSucc := by
                apply Fin.ext
                rw [Fin.val_succ]
                change i.val + 1 = m
                omega
              exact hA hAs
            · intro hcon
              have hiv : i.val = m := hcon
              have hBs : i.succ =
                  ((⟨m + 1, by omega⟩ : Fin (m + 2))).castSucc := by
                apply Fin.ext
                rw [Fin.val_succ]
                change i.val + 1 = m + 1
                omega
              exact hB hBs
          rw [eL, eR]
  have hs'G : s' ∈ ntG (m + 1) := by
    rw [hs'swap]
    have hE : Equiv.swap (⟨m - 1, by omega⟩ : Fin (m + 2)) ⟨m, by omega⟩ ∈
        ntE (m + 1) := by
      constructor
      · have e0 : Equiv.swap (⟨m - 1, by omega⟩ : Fin (m + 2)) ⟨m, by omega⟩
            0 = 0 :=
          ntSwap_fix_vals _ _ _
            (by change (0 : ℕ) ≠ m - 1; omega) (by change (0 : ℕ) ≠ m; omega)
        rw [e0]
        intro hcon
        have hvv := congrArg Fin.val hcon
        simp only [Fin.val_zero, Fin.val_last] at hvv
        omega
      · have eL : Equiv.swap (⟨m - 1, by omega⟩ : Fin (m + 2)) ⟨m, by omega⟩
            (Fin.last (m + 1)) = Fin.last (m + 1) := by
          apply ntSwap_fix_vals
          · change ((Fin.last (m + 1) : Fin (m + 2))).val ≠ m - 1
            rw [Fin.val_last]; omega
          · change ((Fin.last (m + 1) : Fin (m + 2))).val ≠ m
            rw [Fin.val_last]; omega
        rw [eL]
        intro hcon
        have hvv := congrArg Fin.val hcon
        simp only [Fin.val_zero, Fin.val_last] at hvv
        omega
    have hinc : ntInc5 (m + 2)
        (Equiv.swap (⟨m - 1, by omega⟩ : Fin (m + 2)) ⟨m, by omega⟩) := by
      have hfix : ∀ x : Fin (m + 2), x.val ≤ 3 →
          (Equiv.swap (⟨m - 1, by omega⟩ : Fin (m + 2)) ⟨m, by omega⟩) x = x := by
        intro x hx
        apply ntSwap_fix_vals
        · change x.val ≠ m - 1; omega
        · change x.val ≠ m; omega
      refine ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩,
        ⟨m, by omega⟩, by simp, by simp, by simp, (by change 3 < m; omega),
        ?_, ?_, ?_, ?_⟩
      · rw [hfix _ (by simp), hfix _ (by simp), Fin.lt_def]; simp
      · rw [hfix _ (by simp), hfix _ (by simp), Fin.lt_def]; simp
      · rw [hfix _ (by simp), hfix _ (by simp), Fin.lt_def]; simp
      · rw [hfix _ (by simp), Equiv.swap_apply_right]
        change 3 < m - 1
        omega
    exact ntMemG_of_inc5 hm hE hinc
  have hs'sign : Equiv.Perm.sign s' = -1 := by
    rw [hs'swap]
    apply Equiv.Perm.sign_swap
    intro hcon
    have e2 : m - 1 = m := congrArg Fin.val hcon
    omega
  have ht'G : ntOdd m ∈ ntG (m + 1) := ntOdd_memG hm
  have ht'sign : Equiv.Perm.sign (ntOdd m) = -1 := by
    unfold ntOdd
    apply Equiv.Perm.sign_swap
    intro hcon
    have e3 : m = m + 1 := congrArg Fin.val hcon
    omega
  have hst := ntG_sameSign hIH hs'G ht'G (hs'sign.trans ht'sign.symm)
  have hlift := ntEqvGen_ins (0 : Fin (m + 3)) (0 : Fin (m + 3)) hst
  rw [← hs', ntOdd_zero_ins] at hlift
  exact Or.inr (Relation.EqvGen.trans _ _ _ hcongr hlift)

/-- Branch 2: insertions below `last` land in a reference class. -/
private lemma ntIns_branch2 {m : ℕ} (hm : 5 ≤ m)
    (hIH : ∀ ρ ∈ ntG (m + 1),
      Relation.EqvGen (ntMove (m + 2)) ρ (ntEven (m + 2)) ∨
        Relation.EqvGen (ntMove (m + 2)) ρ (ntOdd m))
    {y v : Fin (m + 3)} {ρ : Equiv.Perm (Fin (m + 2))}
    (hρ : ρ ∈ ntG (m + 1))
    (hy1 : y.val ≤ m + 1) (hv1 : v.val ≤ m + 1)
    (hne1 : (y.val, v.val) ≠ (0, m + 1)) (hne2 : (y.val, v.val) ≠ (m + 1, 0)) :
    Relation.EqvGen (ntMove (m + 3)) (ntIns y v ρ) (ntEven (m + 3)) ∨
      Relation.EqvGen (ntMove (m + 3)) (ntIns y v ρ) (ntOdd (m + 1)) := by
  have hy'lt : y.val < m + 3 := y.is_lt
  have hv'lt : v.val < m + 3 := v.is_lt
  set y' : Fin (m + 2) := ⟨y.val, by omega⟩ with hy'def
  set v' : Fin (m + 2) := ⟨v.val, by omega⟩ with hv'def
  have ey : y'.val = y.val := rfl
  have ev : v'.val = v.val := rfl
  have hy : y = y'.castSucc := by
    apply Fin.ext
    rw [Fin.val_castSucc]
  have hv : v = v'.castSucc := by
    apply Fin.ext
    rw [Fin.val_castSucc]
  have hne' : (y' ≠ 0 ∨ v' ≠ Fin.last (m + 1)) ∧
      (y' ≠ Fin.last (m + 1) ∨ v' ≠ 0) := by
    constructor
    · by_contra hc
      simp only [not_or, not_not] at hc
      obtain ⟨hy0, hv0⟩ := hc
      have h1 : y'.val = 0 := by rw [hy0]; exact Fin.val_zero _
      have h2 : v'.val = m + 1 := by rw [hv0]; exact Fin.val_last _
      have hyv : y.val = 0 := by omega
      have hvv : v.val = m + 1 := by omega
      exact hne1 (by rw [hyv, hvv])
    · by_contra hc
      simp only [not_or, not_not] at hc
      obtain ⟨hy0, hv0⟩ := hc
      have h1 : y'.val = m + 1 := by rw [hy0]; exact Fin.val_last _
      have h2 : v'.val = 0 := by rw [hv0]; exact Fin.val_zero _
      have hyv : y.val = m + 1 := by omega
      have hvv : v.val = 0 := by omega
      exact hne2 (by rw [hyv, hvv])
  rcases hIH ρ hρ with hρe | hρo
  · have hμ'G : ntEven (m + 2) ∈ ntG (m + 1) := ntEven_memG hm
    have hρμ : Relation.EqvGen (ntMove (m + 2)) ρ (ntEven (m + 2)) :=
      ntG_sameSign hIH hρ hμ'G (ntEqvGen_sign hρe)
    have hcongr : Relation.EqvGen (ntMove (m + 3)) (ntIns y v ρ)
        (ntIns y v (ntEven (m + 2))) := ntEqvGen_ins y v hρμ
    have hEvenL : ntEven (m + 2) =
        ntIns (Fin.last (m + 1)) (Fin.last (m + 1)) 1 := by
      have e : ntIns (Fin.last (m + 1)) (Fin.last (m + 1))
          (1 : Equiv.Perm (Fin (m + 1))) = 1 := ntIns_last_one
      rw [e]
      rfl
    rw [hEvenL, ntIns_comm_last y v 1 y' v' hy hv] at hcongr
    have hinnerG : ntIns y' v' (1 : Equiv.Perm (Fin (m + 1))) ∈ ntG (m + 1) :=
      ntG_id_ins hm y' v' hne'
    rcases hIH _ hinnerG with hI | hI
    · exact ntIns_closeLast_even hcongr hI
    · have hstep := ntEqvGen_ins (Fin.last (m + 2)) (Fin.last (m + 2)) hI
      exact ntIns_closeLast_odd hm hIH
        (Relation.EqvGen.trans _ _ _ hcongr hstep)
  · have hμ'oddG : ntIns (Fin.last (m + 1)) (Fin.last (m + 1))
        (Equiv.swap (⟨2, by omega⟩ : Fin (m + 1)) ⟨3, by omega⟩) ∈
        ntG (m + 1) := by
      have hE : ntIns (Fin.last (m + 1)) (Fin.last (m + 1))
          (Equiv.swap (⟨2, by omega⟩ : Fin (m + 1)) ⟨3, by omega⟩) ∈
          ntE (m + 1) := by
        have h01 : (0 : Fin (m + 2)) ≠ Fin.last (m + 1) := by
          intro hcon
          have hvv := congrArg Fin.val hcon
          simp only [Fin.val_zero, Fin.val_last] at hvv
          omega
        constructor
        · intro hcon
          obtain ⟨i, hi⟩ :=
            Fin.exists_succAbove_eq (show (0 : Fin (m + 2)) ≠
              Fin.last (m + 1) from h01)
          have hi00 : i = 0 := by
            have e := congrArg Fin.val hi
            rw [Fin.succAbove_last_apply] at e
            rw [Fin.val_castSucc] at e
            have e2 : i.val = 0 := by simpa using e
            exact Fin.ext e2
          subst hi00
          have e2 : ntIns (Fin.last (m + 1)) (Fin.last (m + 1))
              (Equiv.swap (⟨2, by omega⟩ : Fin (m + 1)) ⟨3, by omega⟩) 0 =
              ((0 : Fin (m + 1))).castSucc := by
            rw [← hi, ntIns_apply_succAbove,
              ntSwap_fix_vals _ _ _ (by simp) (by simp),
              Fin.succAbove_last_apply]
          rw [e2] at hcon
          have hvv := congrArg Fin.val hcon
          simp only [Fin.val_castSucc, Fin.val_zero, Fin.val_last] at hvv
          omega
        · rw [ntIns_apply_same]
          intro hcon
          have hvv := congrArg Fin.val hcon
          simp only [Fin.val_zero, Fin.val_last] at hvv
          omega
      have hinc : ntInc5 (m + 2) (ntIns (Fin.last (m + 1)) (Fin.last (m + 1))
          (Equiv.swap (⟨2, by omega⟩ : Fin (m + 1)) ⟨3, by omega⟩)) :=
        ntInc5_swap23_ins hm _ _ _ rfl
      exact ntMemG_of_inc5 hm hE hinc
    have hsign' : Equiv.Perm.sign (ntIns (Fin.last (m + 1)) (Fin.last (m + 1))
        (Equiv.swap (⟨2, by omega⟩ : Fin (m + 1)) ⟨3, by omega⟩)) = -1 := by
      have e : ntIns (Fin.last (m + 1)) (Fin.last (m + 1))
          (Equiv.swap (⟨2, by omega⟩ : Fin (m + 1)) ⟨3, by omega⟩) =
          Equiv.swap ((⟨2, by omega⟩ : Fin (m + 1))).castSucc
            ((⟨3, by omega⟩ : Fin (m + 1))).castSucc := by
        exact ntIns_last_swap _ _
      rw [e]
      apply Equiv.Perm.sign_swap
      intro hcon
      have e2 : (2 : ℕ) = 3 := congrArg Fin.val hcon
      omega
    have hρo_sign : Equiv.Perm.sign ρ = -1 := by
      have e1 := ntEqvGen_sign hρo
      have e2 : Equiv.Perm.sign (ntOdd m) = -1 := by
        unfold ntOdd
        apply Equiv.Perm.sign_swap
        intro hcon
        have e3 : m = m + 1 := congrArg Fin.val hcon
        omega
      rw [e2] at e1
      exact e1
    have hρμ := ntG_sameSign hIH hρ hμ'oddG (hρo_sign.trans hsign'.symm)
    have hcongr := ntEqvGen_ins y v hρμ
    rw [ntIns_comm_last y v _ y' v' hy hv] at hcongr
    have hinnerG := ntG_swap23_ins hm y' v' _ rfl hne'
    rcases hIH _ hinnerG with hI | hI
    · exact ntIns_closeLast_even hcongr hI
    · have hstep := ntEqvGen_ins (Fin.last (m + 2)) (Fin.last (m + 2)) hI
      exact ntIns_closeLast_odd hm hIH
        (Relation.EqvGen.trans _ _ _ hcongr hstep)

/-- The `0-1` swap is generic (used for odd witness move results). -/
private lemma ntSwap01_memG {m : ℕ} (hm : 5 ≤ m) :
    Equiv.swap (⟨0, by omega⟩ : Fin (m + 2))
      (⟨1, by omega⟩ : Fin (m + 2)) ∈ ntG (m + 1) := by
  have hE : Equiv.swap (⟨0, by omega⟩ : Fin (m + 2))
      (⟨1, by omega⟩ : Fin (m + 2)) ∈ ntE (m + 1) := by
    constructor
    · have e0 : Equiv.swap (⟨0, by omega⟩ : Fin (m + 2))
          (⟨1, by omega⟩ : Fin (m + 2)) 0 =
          (⟨1, by omega⟩ : Fin (m + 2)) :=
        Equiv.swap_apply_left _ _
      rw [e0]
      intro hcon
      have hvv := congrArg Fin.val hcon
      simp only [Fin.val_last] at hvv
      omega
    · have eL : Equiv.swap (⟨0, by omega⟩ : Fin (m + 2))
          (⟨1, by omega⟩ : Fin (m + 2)) (Fin.last (m + 1)) =
          Fin.last (m + 1) := by
        apply ntSwap_fix_vals
        · change ((Fin.last (m + 1) : Fin (m + 2))).val ≠ 0
          rw [Fin.val_last]; omega
        · change ((Fin.last (m + 1) : Fin (m + 2))).val ≠ 1
          rw [Fin.val_last]; omega
      rw [eL]
      intro hcon
      have hvv := congrArg Fin.val hcon
      simp only [Fin.val_zero, Fin.val_last] at hvv
      omega
  have hinc : ntInc5 (m + 2) (Equiv.swap (⟨0, by omega⟩ : Fin (m + 2))
      (⟨1, by omega⟩ : Fin (m + 2))) := by
    have hfix : ∀ x : Fin (m + 2), 2 ≤ x.val →
        (Equiv.swap (⟨0, by omega⟩ : Fin (m + 2))
          (⟨1, by omega⟩ : Fin (m + 2))) x = x := by
      intro x hx
      apply ntSwap_fix_vals
      · change x.val ≠ 0; omega
      · change x.val ≠ 1; omega
    refine ⟨⟨2, by omega⟩, ⟨3, by omega⟩, ⟨4, by omega⟩, ⟨5, by omega⟩,
      ⟨6, by omega⟩, by simp, by simp, by simp, by simp, ?_, ?_, ?_, ?_⟩
    · rw [hfix _ (by simp), hfix _ (by simp), Fin.lt_def]; simp
    · rw [hfix _ (by simp), hfix _ (by simp), Fin.lt_def]; simp
    · rw [hfix _ (by simp), hfix _ (by simp), Fin.lt_def]; simp
    · rw [hfix _ (by simp), hfix _ (by simp), Fin.lt_def]; simp
  exact ntMemG_of_inc5 hm hE hinc

/-- Even inner permutation for the `(1, n-1)` witness. -/
private lemma ntMuP1e {m : ℕ} (hm : 5 ≤ m) :
    ∃ μe : Equiv.Perm (Fin (m + 2)),
      μe (⟨0, by omega⟩ : Fin (m + 2)) = (⟨2, by omega⟩ : Fin (m + 2)) ∧
      μe (⟨1, by omega⟩ : Fin (m + 2)) = (⟨0, by omega⟩ : Fin (m + 2)) ∧
      μe (⟨2, by omega⟩ : Fin (m + 2)) = (⟨1, by omega⟩ : Fin (m + 2)) ∧
      μe ∈ ntG (m + 1) ∧ Equiv.Perm.sign μe = 1 ∧
      ∀ x : Fin (m + 2), 3 ≤ x.val → μe x = x := by
  have d01 : (⟨0, by omega⟩ : Fin (m + 2)) ≠ (⟨1, by omega⟩ : Fin (m + 2)) :=
    Fin.ne_of_val_ne (by simp)
  have d02 : (⟨0, by omega⟩ : Fin (m + 2)) ≠ (⟨2, by omega⟩ : Fin (m + 2)) :=
    Fin.ne_of_val_ne (by simp)
  have d10 : (⟨1, by omega⟩ : Fin (m + 2)) ≠ (⟨0, by omega⟩ : Fin (m + 2)) :=
    Fin.ne_of_val_ne (by simp)
  have d12 : (⟨1, by omega⟩ : Fin (m + 2)) ≠ (⟨2, by omega⟩ : Fin (m + 2)) :=
    Fin.ne_of_val_ne (by simp)
  have d20 : (⟨2, by omega⟩ : Fin (m + 2)) ≠ (⟨0, by omega⟩ : Fin (m + 2)) :=
    Fin.ne_of_val_ne (by simp)
  have d21 : (⟨2, by omega⟩ : Fin (m + 2)) ≠ (⟨1, by omega⟩ : Fin (m + 2)) :=
    Fin.ne_of_val_ne (by simp)
  have dL0 : (Fin.last (m + 1) : Fin (m + 2)) ≠ (⟨0, by omega⟩ : Fin (m + 2)) := by
    intro hcon
    have hv := congrArg Fin.val hcon
    simp only [Fin.val_last] at hv
    omega
  have dL1 : (Fin.last (m + 1) : Fin (m + 2)) ≠ (⟨1, by omega⟩ : Fin (m + 2)) := by
    intro hcon
    have hv := congrArg Fin.val hcon
    simp only [Fin.val_last] at hv
    omega
  have dL2 : (Fin.last (m + 1) : Fin (m + 2)) ≠ (⟨2, by omega⟩ : Fin (m + 2)) := by
    intro hcon
    have hv := congrArg Fin.val hcon
    simp only [Fin.val_last] at hv
    omega
  have z0 : (0 : Fin (m + 2)) = (⟨0, by omega⟩ : Fin (m + 2)) := rfl
  have hfix : ∀ x : Fin (m + 2), 3 ≤ x.val →
      (Equiv.swap (⟨0, by omega⟩ : Fin (m + 2))
        (⟨1, by omega⟩ : Fin (m + 2)) *
      Equiv.swap (⟨0, by omega⟩ : Fin (m + 2))
        (⟨2, by omega⟩ : Fin (m + 2))) x = x := by
    intro x hx
    rw [Equiv.Perm.mul_apply]
    have e2 : Equiv.swap (⟨0, by omega⟩ : Fin (m + 2))
        (⟨2, by omega⟩ : Fin (m + 2)) x = x := by
      apply Equiv.swap_apply_of_ne_of_ne
      · intro hcon
        have hv : x.val = 0 := congrArg Fin.val hcon
        omega
      · intro hcon
        have hv : x.val = 2 := congrArg Fin.val hcon
        omega
    have e1 : Equiv.swap (⟨0, by omega⟩ : Fin (m + 2))
        (⟨1, by omega⟩ : Fin (m + 2)) x = x := by
      apply Equiv.swap_apply_of_ne_of_ne
      · intro hcon
        have hv : x.val = 0 := congrArg Fin.val hcon
        omega
      · intro hcon
        have hv : x.val = 1 := congrArg Fin.val hcon
        omega
    rw [e2, e1]
  refine ⟨Equiv.swap (⟨0, by omega⟩ : Fin (m + 2))
      (⟨1, by omega⟩ : Fin (m + 2)) *
    Equiv.swap (⟨0, by omega⟩ : Fin (m + 2))
      (⟨2, by omega⟩ : Fin (m + 2)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne d20 d21]
  · rw [Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne d10 d12, Equiv.swap_apply_right]
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right, Equiv.swap_apply_left]
  · have hE : (Equiv.swap (⟨0, by omega⟩ : Fin (m + 2))
        (⟨1, by omega⟩ : Fin (m + 2)) *
      Equiv.swap (⟨0, by omega⟩ : Fin (m + 2))
        (⟨2, by omega⟩ : Fin (m + 2))) ∈ ntE (m + 1) := by
      constructor
      · rw [z0, Equiv.Perm.mul_apply, Equiv.swap_apply_left,
          Equiv.swap_apply_of_ne_of_ne d20 d21]
        intro hcon
        have hvv := congrArg Fin.val hcon
        simp only [Fin.val_last] at hvv
        omega
      · have eL : (Equiv.swap (⟨0, by omega⟩ : Fin (m + 2))
            (⟨1, by omega⟩ : Fin (m + 2)) *
          Equiv.swap (⟨0, by omega⟩ : Fin (m + 2))
            (⟨2, by omega⟩ : Fin (m + 2))) (Fin.last (m + 1)) =
            Fin.last (m + 1) := by
          rw [Equiv.Perm.mul_apply,
            Equiv.swap_apply_of_ne_of_ne dL0 dL2,
            Equiv.swap_apply_of_ne_of_ne dL0 dL1]
        rw [eL]
        intro hcon
        have hvv := congrArg Fin.val hcon
        simp only [Fin.val_zero, Fin.val_last] at hvv
        omega
    have hinc : ntInc5 (m + 2) (Equiv.swap (⟨0, by omega⟩ : Fin (m + 2))
        (⟨1, by omega⟩ : Fin (m + 2)) *
        Equiv.swap (⟨0, by omega⟩ : Fin (m + 2))
          (⟨2, by omega⟩ : Fin (m + 2))) := by
      refine ⟨⟨1, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩, ⟨4, by omega⟩,
        ⟨5, by omega⟩, by simp, by simp, by simp, by simp, ?_, ?_, ?_, ?_⟩
      · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne d10 d12,
          Equiv.swap_apply_right, Equiv.Perm.mul_apply, Equiv.swap_apply_right,
          Equiv.swap_apply_left]
        simp
      · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right, Equiv.swap_apply_left,
          hfix _ (by simp)]
        change (1 : ℕ) < 3
        omega
      · rw [hfix _ (by simp), hfix _ (by simp), Fin.lt_def]; simp
      · rw [hfix _ (by simp), hfix _ (by simp), Fin.lt_def]; simp
    exact ntMemG_of_inc5 hm hE hinc
  · rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap d01, Equiv.Perm.sign_swap d02]
    decide
  · exact hfix

/-- Odd inner permutation for the `(1, n-1)` witness. -/
private lemma ntMuP1o {m : ℕ} (hm : 5 ≤ m)
    {μe : Equiv.Perm (Fin (m + 2))}
    (f0 : μe (⟨0, by omega⟩ : Fin (m + 2)) = (⟨2, by omega⟩ : Fin (m + 2)))
    (f1 : μe (⟨1, by omega⟩ : Fin (m + 2)) = (⟨0, by omega⟩ : Fin (m + 2)))
    (f2 : μe (⟨2, by omega⟩ : Fin (m + 2)) = (⟨1, by omega⟩ : Fin (m + 2)))
    (hse : Equiv.Perm.sign μe = 1)
    (hfix : ∀ x : Fin (m + 2), 3 ≤ x.val → μe x = x) :
    let μo := μe * Equiv.swap (⟨m, by omega⟩ : Fin (m + 2))
      (⟨m + 1, by omega⟩ : Fin (m + 2))
    μo ∈ ntG (m + 1) ∧ Equiv.Perm.sign μo = -1 := by
  dsimp only
  have dM : (⟨m, by omega⟩ : Fin (m + 2)) ≠
      (⟨m + 1, by omega⟩ : Fin (m + 2)) := by
    intro h
    have := congrArg Fin.val h
    change m = m + 1 at this
    omega
  have Sfix : ∀ x : Fin (m + 2), x.val ≠ m → x.val ≠ m + 1 →
      Equiv.swap (⟨m, by omega⟩ : Fin (m + 2))
        (⟨m + 1, by omega⟩ : Fin (m + 2)) x = x := by
    intro x hxm hxm1
    apply ntSwap_fix_vals
    · exact hxm
    · exact hxm1
  constructor
  · apply ntMemG_of_inc5 hm
    · constructor
      · rw [Equiv.Perm.mul_apply,
          Sfix _ (by change 0 ≠ m; omega) (by change 0 ≠ m + 1; omega)]
        change μe (⟨0, by omega⟩ : Fin (m + 2)) ≠ Fin.last (m + 1)
        rw [f0]
        intro h
        have := congrArg Fin.val h
        simp only [Fin.val_last] at this
        omega
      · have hlast : (Fin.last (m + 1) : Fin (m + 2)) =
            (⟨m + 1, by omega⟩ : Fin (m + 2)) := Fin.ext (Fin.val_last _)
        rw [Equiv.Perm.mul_apply, hlast, Equiv.swap_apply_right,
          hfix _ (show (3 : ℕ) ≤ m from by omega)]
        intro h
        have := congrArg Fin.val h
        change m = 0 at this
        omega
    · have g1 : (μe * Equiv.swap (⟨m, by omega⟩ : Fin (m + 2))
            (⟨m + 1, by omega⟩ : Fin (m + 2))) (⟨1, by omega⟩ : Fin (m + 2)) =
          (⟨0, by omega⟩ : Fin (m + 2)) := by
        rw [Equiv.Perm.mul_apply,
          Sfix _ (by change 1 ≠ m; omega) (by change 1 ≠ m + 1; omega), f1]
      have g2 : (μe * Equiv.swap (⟨m, by omega⟩ : Fin (m + 2))
            (⟨m + 1, by omega⟩ : Fin (m + 2))) (⟨2, by omega⟩ : Fin (m + 2)) =
          (⟨1, by omega⟩ : Fin (m + 2)) := by
        rw [Equiv.Perm.mul_apply,
          Sfix _ (by change 2 ≠ m; omega) (by change 2 ≠ m + 1; omega), f2]
      have g3 : (μe * Equiv.swap (⟨m, by omega⟩ : Fin (m + 2))
            (⟨m + 1, by omega⟩ : Fin (m + 2))) (⟨3, by omega⟩ : Fin (m + 2)) =
          (⟨3, by omega⟩ : Fin (m + 2)) := by
        rw [Equiv.Perm.mul_apply, Sfix _ (by change 3 ≠ m; omega)
          (by change 3 ≠ m + 1; omega), hfix _ (by norm_num)]
      have g4 : (μe * Equiv.swap (⟨m, by omega⟩ : Fin (m + 2))
            (⟨m + 1, by omega⟩ : Fin (m + 2))) (⟨4, by omega⟩ : Fin (m + 2)) =
          (⟨4, by omega⟩ : Fin (m + 2)) := by
        rw [Equiv.Perm.mul_apply, Sfix _ (by change 4 ≠ m; omega)
          (by change 4 ≠ m + 1; omega), hfix _ (by norm_num)]
      have gm : (μe * Equiv.swap (⟨m, by omega⟩ : Fin (m + 2))
            (⟨m + 1, by omega⟩ : Fin (m + 2))) (⟨m, by omega⟩ : Fin (m + 2)) =
          (⟨m + 1, by omega⟩ : Fin (m + 2)) := by
        rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left,
          hfix _ (show (3 : ℕ) ≤ m + 1 from by omega)]
      refine ⟨⟨1, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩, ⟨4, by omega⟩,
        ⟨m, by omega⟩, by simp, by simp, by simp, (by change 4 < m; omega),
        ?_, ?_, ?_, ?_⟩
      · rw [g1, g2, Fin.lt_def]
        simp
      · rw [g2, g3]
        change (1 : ℕ) < 3
        omega
      · rw [g3, g4, Fin.lt_def]
        simp
      · rw [g4, gm]
        change 4 < m + 1
        omega
  · rw [Equiv.Perm.sign_mul, hse, Equiv.Perm.sign_swap dM]
    simp

private lemma ntG_symm_of_inc5 {m : ℕ} (hm : 5 ≤ m)
    {σ : Equiv.Perm (Fin (m + 2))} (hG : σ ∈ ntG (m + 1))
    (hinc : ntInc5 (m + 2) σ) : σ.symm ∈ ntG (m + 1) :=
  ntMemG_of_inc5 hm (ntE_symm hG.1) (ntInc5_symm hinc)

private lemma ntG_rc_of_inc5 {m : ℕ} (hm : 5 ≤ m)
    {σ : Equiv.Perm (Fin (m + 2))} (hG : σ ∈ ntG (m + 1))
    (hinc : ntInc5 (m + 2) σ) : ntRC σ ∈ ntG (m + 1) :=
  ntMemG_of_inc5 hm (ntE_rc hG.1) (ntInc5_rc hinc)

private lemma ntG_rc_symm_of_inc5 {m : ℕ} (hm : 5 ≤ m)
    {σ : Equiv.Perm (Fin (m + 2))} (hG : σ ∈ ntG (m + 1))
    (hinc : ntInc5 (m + 2) σ) : ntRC σ.symm ∈ ntG (m + 1) :=
  ntG_rc_of_inc5 hm (ntG_symm_of_inc5 hm hG hinc) (ntInc5_symm hinc)

private lemma ntInsertion_pair1 {m : ℕ} (hm : 5 ≤ m)
    (hIH : ∀ ρ ∈ ntG (m + 1),
      Relation.EqvGen (ntMove (m + 2)) ρ (ntEven (m + 2)) ∨
        Relation.EqvGen (ntMove (m + 2)) ρ (ntOdd m))
    {ρ : Equiv.Perm (Fin (m + 2))} (hρ : ρ ∈ ntG (m + 1)) :
    Relation.EqvGen (ntMove (m + 3))
        (ntIns (⟨1, by omega⟩ : Fin (m + 3)) (⟨m + 2, by omega⟩ : Fin (m + 3)) ρ)
        (ntEven (m + 3)) ∨
      Relation.EqvGen (ntMove (m + 3))
        (ntIns (⟨1, by omega⟩ : Fin (m + 3)) (⟨m + 2, by omega⟩ : Fin (m + 3)) ρ)
        (ntOdd (m + 1)) := by
  obtain ⟨μe, f0, f1, f2, hμe, hse, hfix⟩ := ntMuP1e hm
  let μo := μe * Equiv.swap (⟨m, by omega⟩ : Fin (m + 2))
    (⟨m + 1, by omega⟩ : Fin (m + 2))
  have hμo : μo ∈ ntG (m + 1) := (ntMuP1o hm f0 f1 f2 hse hfix).1
  have hso : Equiv.Perm.sign μo = -1 := (ntMuP1o hm f0 f1 f2 hse hfix).2
  have hste := ntPair1e_step hm
    (y := (⟨1, by omega⟩ : Fin (m + 3)))
    (v := (⟨m + 2, by omega⟩ : Fin (m + 3))) ⟨rfl, rfl⟩ f0 f1 f2 hfix
  have hsto := ntPair1o_step hm
    (y := (⟨1, by omega⟩ : Fin (m + 3)))
    (v := (⟨m + 2, by omega⟩ : Fin (m + 3))) ⟨rfl, rfl⟩ f0 f1 f2 hfix
  have hce := ntIns_branch1 hm hIH (y := (⟨3, by omega⟩ : Fin (m + 3)))
    (v := (⟨m + 2, by omega⟩ : Fin (m + 3))) (hρ := ntEven_memG hm)
    (by norm_num) (by change 1 ≤ m + 2; omega)
    (by
      intro h
      have h' := congrArg Prod.fst h
      simp at h')
    (by
      intro h
      have h' := congrArg Prod.fst h
      dsimp at h'
      omega)
  have hco := ntIns_branch1 hm hIH (y := (⟨3, by omega⟩ : Fin (m + 3)))
    (v := (⟨m + 2, by omega⟩ : Fin (m + 3))) (hρ := ntOdd_memG hm)
    (by norm_num) (by change 1 ≤ m + 2; omega)
    (by
      intro h
      have h' := congrArg Prod.fst h
      simp at h')
    (by
      intro h
      have h' := congrArg Prod.fst h
      dsimp at h'
      omega)
  exact ntIns_parity_transfer hIH hρ hμe hse hμo hso hste hsto hce hco

private lemma ntInsertion_pair3 {m : ℕ} (hm : 5 ≤ m)
    (hIH : ∀ ρ ∈ ntG (m + 1),
      Relation.EqvGen (ntMove (m + 2)) ρ (ntEven (m + 2)) ∨
        Relation.EqvGen (ntMove (m + 2)) ρ (ntOdd m))
    {ρ : Equiv.Perm (Fin (m + 2))} (hρ : ρ ∈ ntG (m + 1)) :
    Relation.EqvGen (ntMove (m + 3))
        (ntIns (⟨m + 2, by omega⟩ : Fin (m + 3)) (⟨1, by omega⟩ : Fin (m + 3)) ρ)
        (ntEven (m + 3)) ∨
      Relation.EqvGen (ntMove (m + 3))
        (ntIns (⟨m + 2, by omega⟩ : Fin (m + 3)) (⟨1, by omega⟩ : Fin (m + 3)) ρ)
        (ntOdd (m + 1)) := by
  obtain ⟨μe, f0, f1, f2, hμe, hse, hfix⟩ := ntMuP1e hm
  let μo := μe * Equiv.swap (⟨m, by omega⟩ : Fin (m + 2))
    (⟨m + 1, by omega⟩ : Fin (m + 2))
  have hμo : μo ∈ ntG (m + 1) := (ntMuP1o hm f0 f1 f2 hse hfix).1
  have hso : Equiv.Perm.sign μo = -1 := (ntMuP1o hm f0 f1 f2 hse hfix).2
  have hince := ntMuP1e_inc hm f1 f2 hfix
  have hinco := ntMuP1o_inc hm f1 f2 hfix
  have hμes : μe.symm ∈ ntG (m + 1) := ntG_symm_of_inc5 hm hμe hince
  have hμos : μo.symm ∈ ntG (m + 1) := ntG_symm_of_inc5 hm hμo hinco
  have hses : Equiv.Perm.sign μe.symm = 1 := by
    rw [Equiv.Perm.sign_symm, hse]
  have hsos : Equiv.Perm.sign μo.symm = -1 := by
    rw [Equiv.Perm.sign_symm, hso]
  have hste : Relation.EqvGen (ntMove (m + 3))
      (ntIns (⟨m + 2, by omega⟩ : Fin (m + 3)) (⟨1, by omega⟩ : Fin (m + 3)) μe.symm)
      (ntIns (⟨m + 2, by omega⟩ : Fin (m + 3)) (⟨3, by omega⟩ : Fin (m + 3)) 1) := by
    have h := ntEqvGen_symm (ntPair1e_step hm
      (y := (⟨1, by omega⟩ : Fin (m + 3)))
      (v := (⟨m + 2, by omega⟩ : Fin (m + 3))) ⟨rfl, rfl⟩ f0 f1 f2 hfix)
    have hone : (1 : Equiv.Perm (Fin (m + 2))).symm = 1 := rfl
    simpa only [ntIns_symm, hone] using h
  have hsto : Relation.EqvGen (ntMove (m + 3))
      (ntIns (⟨m + 2, by omega⟩ : Fin (m + 3)) (⟨1, by omega⟩ : Fin (m + 3)) μo.symm)
      (ntIns (⟨m + 2, by omega⟩ : Fin (m + 3)) (⟨3, by omega⟩ : Fin (m + 3))
        (ntOdd m)) := by
    have h := ntEqvGen_symm (ntPair1o_step hm
      (y := (⟨1, by omega⟩ : Fin (m + 3)))
      (v := (⟨m + 2, by omega⟩ : Fin (m + 3))) ⟨rfl, rfl⟩ f0 f1 f2 hfix)
    simpa only [ntIns_symm, ntOdd_symm] using h
  have hce := ntIns_branch1 hm hIH (y := (⟨m + 2, by omega⟩ : Fin (m + 3)))
    (v := (⟨3, by omega⟩ : Fin (m + 3))) (hρ := ntEven_memG hm)
    (by change 1 ≤ m + 2; omega) (by norm_num)
    (by
      intro h
      have h' := congrArg Prod.fst h
      dsimp at h'
      omega)
    (by
      intro h
      have h' := congrArg Prod.snd h
      simp at h')
  have hco := ntIns_branch1 hm hIH (y := (⟨m + 2, by omega⟩ : Fin (m + 3)))
    (v := (⟨3, by omega⟩ : Fin (m + 3))) (hρ := ntOdd_memG hm)
    (by change 1 ≤ m + 2; omega) (by norm_num)
    (by
      intro h
      have h' := congrArg Prod.fst h
      dsimp at h'
      omega)
    (by
      intro h
      have h' := congrArg Prod.snd h
      simp at h')
  exact ntIns_parity_transfer hIH hρ hμes hses hμos hsos hste hsto hce hco

private lemma ntInsertion_pair2 {m : ℕ} (hm : 5 ≤ m)
    (hIH : ∀ ρ ∈ ntG (m + 1),
      Relation.EqvGen (ntMove (m + 2)) ρ (ntEven (m + 2)) ∨
        Relation.EqvGen (ntMove (m + 2)) ρ (ntOdd m))
    {ρ : Equiv.Perm (Fin (m + 2))} (hρ : ρ ∈ ntG (m + 1)) :
    Relation.EqvGen (ntMove (m + 3))
        (ntIns (⟨m + 1, by omega⟩ : Fin (m + 3)) (⟨0, by omega⟩ : Fin (m + 3)) ρ)
        (ntEven (m + 3)) ∨
      Relation.EqvGen (ntMove (m + 3))
        (ntIns (⟨m + 1, by omega⟩ : Fin (m + 3)) (⟨0, by omega⟩ : Fin (m + 3)) ρ)
        (ntOdd (m + 1)) := by
  obtain ⟨μe, f0, f1, f2, hμe, hse, hfix⟩ := ntMuP1e hm
  let μo := μe * Equiv.swap (⟨m, by omega⟩ : Fin (m + 2))
    (⟨m + 1, by omega⟩ : Fin (m + 2))
  have hμo : μo ∈ ntG (m + 1) := (ntMuP1o hm f0 f1 f2 hse hfix).1
  have hso : Equiv.Perm.sign μo = -1 := (ntMuP1o hm f0 f1 f2 hse hfix).2
  have hince := ntMuP1e_inc hm f1 f2 hfix
  have hinco := ntMuP1o_inc hm f1 f2 hfix
  have hμer : ntRC μe ∈ ntG (m + 1) := ntG_rc_of_inc5 hm hμe hince
  have hμor : ntRC μo ∈ ntG (m + 1) := ntG_rc_of_inc5 hm hμo hinco
  have hser : Equiv.Perm.sign (ntRC μe) = 1 := by rw [ntRC_sign, hse]
  have hsor : Equiv.Perm.sign (ntRC μo) = -1 := by rw [ntRC_sign, hso]
  have hr1 : (⟨1, by omega⟩ : Fin (m + 3)).rev =
      (⟨m + 1, by omega⟩ : Fin (m + 3)) := by
    apply Fin.ext
    simp
  have hr3 : (⟨3, by omega⟩ : Fin (m + 3)).rev =
      (⟨m - 1, by omega⟩ : Fin (m + 3)) := by
    apply Fin.ext
    simp
  have hrL : (⟨m + 2, by omega⟩ : Fin (m + 3)).rev =
      (⟨0, by omega⟩ : Fin (m + 3)) := by
    apply Fin.ext
    simp
  have hste : Relation.EqvGen (ntMove (m + 3))
      (ntIns (⟨m + 1, by omega⟩ : Fin (m + 3)) (⟨0, by omega⟩ : Fin (m + 3)) (ntRC μe))
      (ntIns (⟨m - 1, by omega⟩ : Fin (m + 3)) (⟨0, by omega⟩ : Fin (m + 3)) 1) := by
    have h := ntEqvGen_rc (ntPair1e_step hm
      (y := (⟨1, by omega⟩ : Fin (m + 3)))
      (v := (⟨m + 2, by omega⟩ : Fin (m + 3))) ⟨rfl, rfl⟩ f0 f1 f2 hfix)
    rw [ntRC_ins, ntRC_ins, hr1, hr3, hrL, ntRC_one] at h
    exact h
  have hsto : Relation.EqvGen (ntMove (m + 3))
      (ntIns (⟨m + 1, by omega⟩ : Fin (m + 3)) (⟨0, by omega⟩ : Fin (m + 3)) (ntRC μo))
      (ntIns (⟨m - 1, by omega⟩ : Fin (m + 3)) (⟨0, by omega⟩ : Fin (m + 3))
        (Equiv.swap (⟨0, by omega⟩ : Fin (m + 2)) ⟨1, by omega⟩)) := by
    have h := ntEqvGen_rc (ntPair1o_step hm
      (y := (⟨1, by omega⟩ : Fin (m + 3)))
      (v := (⟨m + 2, by omega⟩ : Fin (m + 3))) ⟨rfl, rfl⟩ f0 f1 f2 hfix)
    rw [ntRC_ins, ntRC_ins, hr1, hr3, hrL, ntRC_odd] at h
    exact h
  have hce := ntIns_branch2 hm hIH (y := (⟨m - 1, by omega⟩ : Fin (m + 3)))
    (v := (⟨0, by omega⟩ : Fin (m + 3))) (hρ := ntEven_memG hm)
    (by change m - 1 ≤ m + 1; omega) (by norm_num)
    (by
      intro h
      have h' := congrArg Prod.snd h
      dsimp at h'
      omega)
    (by
      intro h
      have h' := congrArg Prod.fst h
      dsimp at h'
      omega)
  have hco := ntIns_branch2 hm hIH (y := (⟨m - 1, by omega⟩ : Fin (m + 3)))
    (v := (⟨0, by omega⟩ : Fin (m + 3))) (hρ := ntSwap01_memG hm)
    (by change m - 1 ≤ m + 1; omega) (by norm_num)
    (by
      intro h
      have h' := congrArg Prod.snd h
      dsimp at h'
      omega)
    (by
      intro h
      have h' := congrArg Prod.fst h
      dsimp at h'
      omega)
  exact ntIns_parity_transfer hIH hρ hμer hser hμor hsor hste hsto hce hco

private lemma ntInsertion_pair4 {m : ℕ} (hm : 5 ≤ m)
    (hIH : ∀ ρ ∈ ntG (m + 1),
      Relation.EqvGen (ntMove (m + 2)) ρ (ntEven (m + 2)) ∨
        Relation.EqvGen (ntMove (m + 2)) ρ (ntOdd m))
    {ρ : Equiv.Perm (Fin (m + 2))} (hρ : ρ ∈ ntG (m + 1)) :
    Relation.EqvGen (ntMove (m + 3))
        (ntIns (⟨0, by omega⟩ : Fin (m + 3)) (⟨m + 1, by omega⟩ : Fin (m + 3)) ρ)
        (ntEven (m + 3)) ∨
      Relation.EqvGen (ntMove (m + 3))
        (ntIns (⟨0, by omega⟩ : Fin (m + 3)) (⟨m + 1, by omega⟩ : Fin (m + 3)) ρ)
        (ntOdd (m + 1)) := by
  obtain ⟨μe, f0, f1, f2, hμe, hse, hfix⟩ := ntMuP1e hm
  let μo := μe * Equiv.swap (⟨m, by omega⟩ : Fin (m + 2))
    (⟨m + 1, by omega⟩ : Fin (m + 2))
  have hμo : μo ∈ ntG (m + 1) := (ntMuP1o hm f0 f1 f2 hse hfix).1
  have hso : Equiv.Perm.sign μo = -1 := (ntMuP1o hm f0 f1 f2 hse hfix).2
  have hince := ntMuP1e_inc hm f1 f2 hfix
  have hinco := ntMuP1o_inc hm f1 f2 hfix
  have hμers : ntRC μe.symm ∈ ntG (m + 1) := ntG_rc_symm_of_inc5 hm hμe hince
  have hμors : ntRC μo.symm ∈ ntG (m + 1) := ntG_rc_symm_of_inc5 hm hμo hinco
  have hsers : Equiv.Perm.sign (ntRC μe.symm) = 1 := by
    rw [ntRC_sign, Equiv.Perm.sign_symm, hse]
  have hsors : Equiv.Perm.sign (ntRC μo.symm) = -1 := by
    rw [ntRC_sign, Equiv.Perm.sign_symm, hso]
  have hr1 : (⟨1, by omega⟩ : Fin (m + 3)).rev =
      (⟨m + 1, by omega⟩ : Fin (m + 3)) := by
    apply Fin.ext
    simp
  have hr3 : (⟨3, by omega⟩ : Fin (m + 3)).rev =
      (⟨m - 1, by omega⟩ : Fin (m + 3)) := by
    apply Fin.ext
    simp
  have hrL : (⟨m + 2, by omega⟩ : Fin (m + 3)).rev =
      (⟨0, by omega⟩ : Fin (m + 3)) := by
    apply Fin.ext
    simp
  have hste : Relation.EqvGen (ntMove (m + 3))
      (ntIns (⟨0, by omega⟩ : Fin (m + 3)) (⟨m + 1, by omega⟩ : Fin (m + 3))
        (ntRC μe.symm))
      (ntIns (⟨0, by omega⟩ : Fin (m + 3)) (⟨m - 1, by omega⟩ : Fin (m + 3)) 1) := by
    have h := ntEqvGen_symm (ntPair1e_step hm
      (y := (⟨1, by omega⟩ : Fin (m + 3)))
      (v := (⟨m + 2, by omega⟩ : Fin (m + 3))) ⟨rfl, rfl⟩ f0 f1 f2 hfix)
    have hone : (1 : Equiv.Perm (Fin (m + 2))).symm = 1 := rfl
    rw [ntIns_symm, ntIns_symm, hone] at h
    have h := ntEqvGen_rc h
    rw [ntRC_ins, ntRC_ins, hr1, hr3, hrL, ntRC_one] at h
    exact h
  have hsto : Relation.EqvGen (ntMove (m + 3))
      (ntIns (⟨0, by omega⟩ : Fin (m + 3)) (⟨m + 1, by omega⟩ : Fin (m + 3))
        (ntRC μo.symm))
      (ntIns (⟨0, by omega⟩ : Fin (m + 3)) (⟨m - 1, by omega⟩ : Fin (m + 3))
        (Equiv.swap (⟨0, by omega⟩ : Fin (m + 2)) ⟨1, by omega⟩)) := by
    have h := ntEqvGen_symm (ntPair1o_step hm
      (y := (⟨1, by omega⟩ : Fin (m + 3)))
      (v := (⟨m + 2, by omega⟩ : Fin (m + 3))) ⟨rfl, rfl⟩ f0 f1 f2 hfix)
    rw [ntIns_symm, ntIns_symm, ntOdd_symm] at h
    have h := ntEqvGen_rc h
    rw [ntRC_ins, ntRC_ins, hr1, hr3, hrL, ntRC_odd] at h
    exact h
  have hce := ntIns_branch2 hm hIH (y := (⟨0, by omega⟩ : Fin (m + 3)))
    (v := (⟨m - 1, by omega⟩ : Fin (m + 3))) (hρ := ntEven_memG hm)
    (by norm_num) (by change m - 1 ≤ m + 1; omega)
    (by
      intro h
      have h' := congrArg Prod.snd h
      dsimp at h'
      omega)
    (by
      intro h
      have h' := congrArg Prod.fst h
      simp at h')
  have hco := ntIns_branch2 hm hIH (y := (⟨0, by omega⟩ : Fin (m + 3)))
    (v := (⟨m - 1, by omega⟩ : Fin (m + 3))) (hρ := ntSwap01_memG hm)
    (by norm_num) (by change m - 1 ≤ m + 1; omega)
    (by
      intro h
      have h' := congrArg Prod.snd h
      dsimp at h'
      omega)
    (by
      intro h
      have h' := congrArg Prod.fst h
      simp at h')
  exact ntIns_parity_transfer hIH hρ hμers hsers hμors hsors hste hsto hce hco

private def ntDefect {n : ℕ} (π : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n) :=
  finRotate n * π * finRotate n * π.symm

private def ntBreaks {n : ℕ} (π : Equiv.Perm (Fin n)) : Finset (Fin n) :=
  (ntDefect π).support.map π.symm.toEmbedding

private lemma ntBeta_eq_cycle_rev {n j : ℕ} (hj : j + 1 ≤ n) :
    ntBeta n j hj = finCycle (⟨j, by omega⟩ : Fin n) *
      (Fin.revPerm : Equiv.Perm (Fin n)) := by
  apply Equiv.Perm.ext
  intro i
  apply Fin.ext
  rw [ntBeta_val, Equiv.Perm.mul_apply, finCycle_apply, Fin.revPerm_apply,
    Fin.val_add_eq_ite]
  simp only [Fin.val_rev]
  by_cases hij : i.val < j
  · rw [ite_eq_left hij]
    split <;> omega
  · rw [ite_eq_right hij]
    split <;> omega

private lemma ntBeta_breaks_eq_empty {n j : ℕ} (hj : j + 1 ≤ n) :
    ntBreaks (ntBeta n j hj) = ∅ := by
  let _ : NeZero n := ⟨by omega⟩
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  rw [nt_mem_breaks_iff] at hi
  apply hi
  rw [ntBeta_eq_cycle_rev hj]
  simp only [Equiv.Perm.mul_apply, finCycle_apply, Fin.revPerm_apply,
    finRotate_apply, finRotate_symm_apply]
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  simp only [← Fin.last_sub]
  abel

private lemma nt_exists_beta_of_breaks_empty {n : ℕ} (hn : 0 < n)
    {π : Equiv.Perm (Fin n)} (hbreak : ntBreaks π = ∅) :
    ∃ j : ℕ, ∃ hj : j + 1 ≤ n, π = ntBeta n j hj := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hgood : ∀ i : Fin (r + 1),
      π (finRotate (r + 1) i) = (finRotate (r + 1)).symm (π i) := by
    intro i
    by_contra h
    have hi : i ∈ ntBreaks π := (nt_mem_breaks_iff π i).2 h
    rw [hbreak] at hi
    simp at hi
  let jf : Fin (r + 1) := π 0 + 1
  have hform : ∀ k : ℕ, ∀ hk : k < r + 1,
      π (⟨k, hk⟩ : Fin (r + 1)) = (⟨k, hk⟩ : Fin (r + 1)).rev + jf := by
    intro k
    induction k with
    | zero =>
        intro hk
        rw [← Fin.last_sub]
        have hlast : Fin.last r = (-1 : Fin (r + 1)) := by
          apply Fin.ext
          simp
        rw [hlast]
        have hz : (⟨0, hk⟩ : Fin (r + 1)) = 0 := Fin.ext rfl
        rw [hz]
        simp only [sub_zero, jf]
        abel
    | succ k ih =>
        intro hk
        have hkr : k < r := by omega
        have hg := hgood (⟨k, by omega⟩ : Fin (r + 1))
        rw [finRotate_of_lt hkr, finRotate_symm_apply, ih (by omega)] at hg
        rw [hg]
        have hs : (⟨k + 1, hk⟩ : Fin (r + 1)) =
            (⟨k, by omega⟩ : Fin (r + 1)) + 1 := by
          apply Fin.ext
          rw [Fin.val_add_one_of_lt' (by change k + 1 < r + 1; omega)]
        rw [hs, ← Fin.last_sub, ← Fin.last_sub]
        abel
  refine ⟨jf.val, jf.is_lt, ?_⟩
  rw [ntBeta_eq_cycle_rev jf.is_lt]
  apply Equiv.Perm.ext
  intro i
  rw [hform i.val i.is_lt]
  simp only [Equiv.Perm.mul_apply, finCycle_apply, Fin.revPerm_apply]

private def ntBreakMap {m : ℕ} (y v : Fin (m + 1))
    (ρ : Equiv.Perm (Fin m)) (z : Fin m) : Fin (m + 1) :=
  let w := y.succAbove z
  if finRotate (m + 1) w = y then
    if w ∈ ntBreaks (ntIns y v ρ) then w else y
  else w

private def ntSemi {n : ℕ} (π : Equiv.Perm (Fin n)) : Prop :=
  ∃ j : ℕ, ∃ hj : j + 1 ≤ n, π = ntBeta n j hj

private lemma ntSemi_iff_breaks_empty {n : ℕ} (hn : 0 < n)
    (π : Equiv.Perm (Fin n)) : ntSemi π ↔ ntBreaks π = ∅ := by
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ntBeta_breaks_eq_empty hj
  · exact nt_exists_beta_of_breaks_empty hn

private lemma ntBreaks_ins_eq_triple {m : ℕ} (hm : 0 < m)
    (p v : Fin (m + 1)) (ρ : Equiv.Perm (Fin m))
    (hρ : ntBreaks ρ = ∅) (hnot : ¬ntSemi (ntIns p v ρ)) :
    ntBreaks (ntIns p v ρ) =
      {(finRotate (m + 1)).symm p, p,
        (ntIns p v ρ).symm (finRotate (m + 1) v)} := by
  let α := ntIns p v ρ
  have hsub : ntBreaks α ⊆
      {(finRotate (m + 1)).symm p, p, α.symm (finRotate (m + 1) v)} :=
    ntBreaks_ins_subset hm p v ρ hρ
  have htriple :
      ({(finRotate (m + 1)).symm p, p,
        α.symm (finRotate (m + 1) v)} : Finset (Fin (m + 1))).card ≤ 3 := by
    have hA := Finset.card_insert_le ((finRotate (m + 1)).symm p)
      ({p, α.symm (finRotate (m + 1) v)} : Finset (Fin (m + 1)))
    have hB := Finset.card_insert_le p
      ({α.symm (finRotate (m + 1) v)} : Finset (Fin (m + 1)))
    have hC : ({α.symm (finRotate (m + 1) v)} : Finset (Fin (m + 1))).card = 1 := by
      simp
    omega
  have hle : (ntBreaks α).card ≤ 3 :=
    le_trans (Finset.card_le_card hsub) htriple
  have h0 : (ntBreaks α).card ≠ 0 := by
    intro h
    apply hnot
    rw [ntSemi_iff_breaks_empty (by omega)]
    exact Finset.card_eq_zero.mp h
  have h1 : (ntBreaks α).card ≠ 1 := nt_card_breaks_ne_one α
  have h2 : (ntBreaks α).card ≠ 2 := nt_card_breaks_ne_two α
  have hcard : (ntBreaks α).card = 3 := by omega
  apply Finset.eq_of_subset_of_card_le hsub
  rw [hcard]
  exact htriple

private noncomputable def ntDSemi {m : ℕ} (α : Equiv.Perm (Fin (m + 1))) :
    Finset (Fin (m + 1)) := by
  classical
  exact Finset.univ.filter fun y =>
    ∃ ρ : Equiv.Perm (Fin m), α = ntIns y (α y) ρ ∧ ntSemi ρ

private lemma ntDSemi_pair_mem {m : ℕ} (hm : 0 < m)
    {α : Equiv.Perm (Fin (m + 1))} (hα : ¬ntSemi α)
    {y : Fin (m + 1)} (hy : y ∈ ntDSemi α) :
    (finRotate (m + 1)).symm y ∈ ntBreaks α ∧ y ∈ ntBreaks α := by
  obtain ⟨ρ, hαρ, hρ⟩ := (nt_mem_DSemi_iff α y).1 hy
  have hρempty : ntBreaks ρ = ∅ :=
    (ntSemi_iff_breaks_empty hm ρ).1 hρ
  have hinsnot : ¬ntSemi (ntIns y (α y) ρ) := by
    rwa [← hαρ]
  have hbreaks := ntBreaks_ins_eq_triple hm y (α y) ρ hρempty hinsnot
  rw [← hαρ] at hbreaks
  rw [hbreaks]
  simp

private lemma ntBreaks_card_eq_three_of_mem_DSemi {m : ℕ} (hm : 0 < m)
    {α : Equiv.Perm (Fin (m + 1))} (hα : ¬ntSemi α)
    {y : Fin (m + 1)} (hy : y ∈ ntDSemi α) : (ntBreaks α).card = 3 := by
  obtain ⟨ρ, hαρ, hρ⟩ := (nt_mem_DSemi_iff α y).1 hy
  have hρempty : ntBreaks ρ = ∅ := (ntSemi_iff_breaks_empty hm ρ).1 hρ
  have hsub : ntBreaks α ⊆
      {(finRotate (m + 1)).symm y, y,
        α.symm (finRotate (m + 1) (α y))} := by
    rw [hαρ]
    simpa only [ntIns_apply_same] using
      ntBreaks_ins_subset hm y (α y) ρ hρempty
  have htriple :
      ({(finRotate (m + 1)).symm y, y,
        α.symm (finRotate (m + 1) (α y))} : Finset (Fin (m + 1))).card ≤ 3 := by
    have hA := Finset.card_insert_le ((finRotate (m + 1)).symm y)
      ({y, α.symm (finRotate (m + 1) (α y))} : Finset (Fin (m + 1)))
    have hB := Finset.card_insert_le y
      ({α.symm (finRotate (m + 1) (α y))} : Finset (Fin (m + 1)))
    have hC : ({α.symm (finRotate (m + 1) (α y))} :
        Finset (Fin (m + 1))).card = 1 := by simp
    omega
  have hle : (ntBreaks α).card ≤ 3 := by
    calc
      (ntBreaks α).card ≤
          ({(finRotate (m + 1)).symm y, y,
            α.symm (finRotate (m + 1) (α y))} : Finset (Fin (m + 1))).card :=
        Finset.card_le_card hsub
      _ ≤ 3 := htriple
  have hne0 : (ntBreaks α).card ≠ 0 := by
    intro h
    apply hα
    rw [ntSemi_iff_breaks_empty (by omega)]
    exact Finset.card_eq_zero.mp h
  have hne1 := nt_card_breaks_ne_one α
  have hne2 := nt_card_breaks_ne_two α
  omega

private lemma ntDSemi_card_le_two {m : ℕ} (hm : 3 ≤ m)
    {α : Equiv.Perm (Fin (m + 1))} (hα : ¬ntSemi α) :
    (ntDSemi α).card ≤ 2 := by
  classical
  by_contra hle
  have hlt : 2 < (ntDSemi α).card := by omega
  obtain ⟨y₁, y₂, y₃, hy₁, hy₂, hy₃, hy₁₂, hy₁₃, hy₂₃⟩ :=
    Finset.two_lt_card_iff.mp hlt
  obtain ⟨ρ, hαρ, hρ⟩ := (nt_mem_DSemi_iff α y₁).1 hy₁
  have hρempty : ntBreaks ρ = ∅ :=
    (ntSemi_iff_breaks_empty (by omega) ρ).1 hρ
  have hinsnot : ¬ntSemi (ntIns y₁ (α y₁) ρ) := by
    rwa [← hαρ]
  have hbreaks :=
    ntBreaks_ins_eq_triple (by omega) y₁ (α y₁) ρ hρempty hinsnot
  rw [← hαρ] at hbreaks
  have hy₂pair := ntDSemi_pair_mem (by omega) hα hy₂
  have hy₃pair := ntDSemi_pair_mem (by omega) hα hy₃
  have hy₂cases :
      y₂ = (finRotate (m + 1)).symm y₁ ∨ y₂ = y₁ ∨
        y₂ = α.symm (finRotate (m + 1) (α y₁)) := by
    rw [hbreaks] at hy₂pair
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hy₂pair.2
  have hy₃cases :
      y₃ = (finRotate (m + 1)).symm y₁ ∨ y₃ = y₁ ∨
        y₃ = α.symm (finRotate (m + 1) (α y₁)) := by
    rw [hbreaks] at hy₃pair
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hy₃pair.2
  have hy₂two :
      y₂ = (finRotate (m + 1)).symm y₁ ∨
        y₂ = α.symm (finRotate (m + 1) (α y₁)) := by
    rcases hy₂cases with h | h | h
    · exact Or.inl h
    · exact False.elim (hy₁₂ h.symm)
    · exact Or.inr h
  have hy₃two :
      y₃ = (finRotate (m + 1)).symm y₁ ∨
        y₃ = α.symm (finRotate (m + 1) (α y₁)) := by
    rcases hy₃cases with h | h | h
    · exact Or.inl h
    · exact False.elim (hy₁₃ h.symm)
    · exact Or.inr h
  have himpossible
      (hp : (finRotate (m + 1)).symm
          ((finRotate (m + 1)).symm y₁) ∈ ntBreaks α)
      (hs : (finRotate (m + 1)).symm
          (α.symm (finRotate (m + 1) (α y₁))) ∈ ntBreaks α) : False := by
    have hpCases := hp
    rw [hbreaks] at hpCases
    simp only [Finset.mem_insert, Finset.mem_singleton] at hpCases
    have hpPrev : (finRotate (m + 1)).symm
        ((finRotate (m + 1)).symm y₁) ≠
          (finRotate (m + 1)).symm y₁ :=
      ntRotate_symm_ne_self (by omega)
        ((finRotate (m + 1)).symm y₁)
    have hpSelf : (finRotate (m + 1)).symm
        ((finRotate (m + 1)).symm y₁) ≠ y₁ :=
      ntRotate_symm_sq_ne_self (by omega) y₁
    have hcross : (finRotate (m + 1)).symm
        ((finRotate (m + 1)).symm y₁) =
          α.symm (finRotate (m + 1) (α y₁)) := by
      rcases hpCases with h | h | h
      · exact False.elim (hpPrev h)
      · exact False.elim (hpSelf h)
      · exact h
    have hsCases := hs
    rw [hbreaks] at hsCases
    rw [← hcross] at hsCases
    simp only [Finset.mem_insert, Finset.mem_singleton] at hsCases
    have hcPrev : (finRotate (m + 1)).symm
        ((finRotate (m + 1)).symm ((finRotate (m + 1)).symm y₁)) ≠
          (finRotate (m + 1)).symm y₁ := by
      intro h
      apply ntRotate_symm_sq_ne_self (by omega) y₁
      exact (finRotate (m + 1)).symm.injective h
    have hcSelf : (finRotate (m + 1)).symm
        ((finRotate (m + 1)).symm ((finRotate (m + 1)).symm y₁)) ≠ y₁ :=
      ntRotate_symm_cube_ne_self (by omega) y₁
    have hcSq : (finRotate (m + 1)).symm
        ((finRotate (m + 1)).symm ((finRotate (m + 1)).symm y₁)) ≠
          (finRotate (m + 1)).symm ((finRotate (m + 1)).symm y₁) :=
      ntRotate_symm_ne_self (by omega)
        ((finRotate (m + 1)).symm ((finRotate (m + 1)).symm y₁))
    rcases hsCases with h | h | h
    · exact hcPrev h
    · exact hcSelf h
    · exact hcSq h
  rcases hy₂two with h₂ | h₂ <;> rcases hy₃two with h₃ | h₃
  · exact hy₂₃ (h₂.trans h₃.symm)
  · apply himpossible
    · rw [h₂] at hy₂pair
      exact hy₂pair.1
    · rw [h₃] at hy₃pair
      exact hy₃pair.1
  · apply himpossible
    · rw [h₃] at hy₃pair
      exact hy₃pair.1
    · rw [h₂] at hy₂pair
      exact hy₂pair.1
  · exact hy₂₃ (h₂.trans h₃.symm)

private structure ntOccurrence {n : ℕ} (σ : Equiv.Perm (Fin n)) where
  a : Fin n
  b : Fin n
  c : Fin n
  d : Fin n
  hab : a.val < b.val
  hbc : b.val < c.val
  hcd : c.val < d.val
  hpat :
    (σ a < σ b ∧ σ b < σ c ∧ σ c < σ d) ∨
      (σ c < σ d ∧ σ d < σ a ∧ σ a < σ b)

private def ntOccurrence.positions {n : ℕ} {σ : Equiv.Perm (Fin n)}
    (o : ntOccurrence σ) : Finset (Fin n) :=
  {o.a, o.b, o.c, o.d}

private lemma nt_mem_breaks_beta_doubleSwap_iff {n j : ℕ} (hj : j + 1 ≤ n)
    {a b c d i : Fin n} :
    i ∈ ntBreaks (ntBeta n j hj * (Equiv.swap a c * Equiv.swap b d)) ↔
      (Equiv.swap a c * Equiv.swap b d : Equiv.Perm (Fin n)) (finRotate n i) ≠
        finRotate n ((Equiv.swap a c * Equiv.swap b d : Equiv.Perm (Fin n)) i) := by
  let _ : NeZero n := ⟨by omega⟩
  let δ := (Equiv.swap a c * Equiv.swap b d : Equiv.Perm (Fin n))
  have hgood (x : Fin n) :
      ntBeta n j hj (finRotate n x) = (finRotate n).symm (ntBeta n j hj x) := by
    by_contra h
    have hx := (nt_mem_breaks_iff (ntBeta n j hj) x).2 h
    rw [ntBeta_breaks_eq_empty hj] at hx
    simp at hx
  rw [nt_mem_breaks_iff]
  change ntBeta n j hj (δ (finRotate n i)) ≠
    (finRotate n).symm (ntBeta n j hj (δ i)) ↔ _
  rw [← hgood (δ i)]
  exact (ntBeta n j hj).injective.ne_iff

private def ntBoundary {n : ℕ} (P : Finset (Fin n)) : Finset (Fin n) :=
  let Q := P.map (finRotate n).symm.toEmbedding
  (P \ Q) ∪ (Q \ P)

private lemma ntBoundary_subset_doubleSwap_breaks {n j : ℕ} (hj : j + 1 ≤ n)
    {a b c d : Fin n} (hab : a.val < b.val) (hbc : b.val < c.val)
    (hcd : c.val < d.val) :
    ntBoundary ({a, b, c, d} : Finset (Fin n)) ⊆
      ntBreaks (ntBeta n j hj * (Equiv.swap a c * Equiv.swap b d)) := by
  let _ : NeZero n := ⟨by omega⟩
  let P : Finset (Fin n) := {a, b, c, d}
  let δ := (Equiv.swap a c * Equiv.swap b d : Equiv.Perm (Fin n))
  have hsupp : δ.support = P := ntDoubleSwap_support hab hbc hcd
  have hmove (x : Fin n) : δ x ≠ x ↔ x ∈ P := by
    rw [← hsupp]
    simp only [Equiv.Perm.mem_support]
  intro i hi
  rw [nt_mem_breaks_beta_doubleSwap_iff hj]
  have hboundary := (nt_mem_boundary_iff P i).1 hi
  by_cases hiP : i ∈ P
  · have hriP : finRotate n i ∉ P := hboundary.mp hiP
    have hfix : δ (finRotate n i) = finRotate n i :=
      Equiv.Perm.notMem_support.mp (by rwa [hsupp])
    rw [hfix]
    intro heq
    have heq' := (finRotate n).injective heq
    exact (hmove i).2 hiP heq'.symm
  · have hriP : finRotate n i ∈ P := by
      by_contra h
      exact hiP (hboundary.mpr h)
    have hfix : δ i = i := Equiv.Perm.notMem_support.mp (by rwa [hsupp])
    rw [hfix]
    exact (hmove (finRotate n i)).2 hriP

private lemma ntDoubleSwap_breaks_of_outside {n j : ℕ} (hj : j + 1 ≤ n)
    {a b c d i : Fin n} (hab : a.val < b.val) (hbc : b.val < c.val)
    (hcd : c.val < d.val)
    (hi : i ∉ ({a, b, c, d} : Finset (Fin n)))
    (hri : finRotate n i ∉ ({a, b, c, d} : Finset (Fin n))) :
    i ∉ ntBreaks (ntBeta n j hj * (Equiv.swap a c * Equiv.swap b d)) := by
  let _ : NeZero n := ⟨by omega⟩
  let P : Finset (Fin n) := {a, b, c, d}
  let δ := (Equiv.swap a c * Equiv.swap b d : Equiv.Perm (Fin n))
  have hsupp : δ.support = P := ntDoubleSwap_support hab hbc hcd
  have hfixi : δ i = i := Equiv.Perm.notMem_support.mp (by rwa [hsupp])
  have hfixri : δ (finRotate n i) = finRotate n i :=
    Equiv.Perm.notMem_support.mp (by rwa [hsupp])
  rw [nt_mem_breaks_beta_doubleSwap_iff hj, hfixi, hfixri]
  simp

private lemma ntDoubleSwap_breaks_card_ge_three {n j : ℕ} (hn : 5 ≤ n)
    (hj : j + 1 ≤ n) {a b c d : Fin n}
    (hab : a.val < b.val) (hbc : b.val < c.val) (hcd : c.val < d.val) :
    3 ≤ (ntBreaks
      (ntBeta n j hj * (Equiv.swap a c * Equiv.swap b d))).card := by
  let _ : NeZero n := ⟨by omega⟩
  let P : Finset (Fin n) := {a, b, c, d}
  let γ := ntBeta n j hj * (Equiv.swap a c * Equiv.swap b d)
  have hab' : a ≠ b := by intro h; subst b; omega
  have hac : a ≠ c := by intro h; subst c; omega
  have had : a ≠ d := by intro h; subst d; omega
  have hbc' : b ≠ c := by intro h; subst c; omega
  have hbd : b ≠ d := by intro h; subst d; omega
  have hcd' : c ≠ d := by intro h; subst d; omega
  have hPcard : P.card = 4 := by
    simp [P, hab', hac, had, hbc', hbd, hcd']
  have hBne : (ntBoundary P).Nonempty := by
    apply ntBoundary_nonempty P (x₀ := a)
    · simp [P]
    · rw [hPcard]
      omega
  have hsub : ntBoundary P ⊆ ntBreaks γ :=
    ntBoundary_subset_doubleSwap_breaks hj hab hbc hcd
  have hnonzero : (ntBreaks γ).card ≠ 0 := by
    intro h
    have hempty := Finset.card_eq_zero.mp h
    obtain ⟨x, hx⟩ := hBne
    have := hsub hx
    rw [hempty] at this
    simp at this
  have hne1 : (ntBreaks γ).card ≠ 1 := nt_card_breaks_ne_one γ
  have hne2 : (ntBreaks γ).card ≠ 2 := nt_card_breaks_ne_two γ
  change 3 ≤ (ntBreaks γ).card
  omega

private lemma ntDoubleSwap_three_shared_outside {n j : ℕ} (hn : 5 ≤ n)
    (hj : j + 1 ≤ n) {a b c d q : Fin n}
    (hab : a.val < b.val) (hbc : b.val < c.val) (hcd : c.val < d.val)
    (hcard : (ntBreaks
      (ntBeta n j hj * (Equiv.swap a c * Equiv.swap b d))).card = 3)
    (hq : q ∉ ({a, b, c, d} : Finset (Fin n)))
    (hprev : (finRotate n).symm q ∈ ntBreaks
      (ntBeta n j hj * (Equiv.swap a c * Equiv.swap b d)))
    (hnext : q ∈ ntBreaks
      (ntBeta n j hj * (Equiv.swap a c * Equiv.swap b d))) : n = 5 := by
  let _ : NeZero n := ⟨by omega⟩
  let P : Finset (Fin n) := {a, b, c, d}
  let γ := ntBeta n j hj * (Equiv.swap a c * Equiv.swap b d)
  let r := finRotate n
  let pred := r.symm q
  have hrpred : r pred = q := r.apply_symm_apply q
  have hrqP : r q ∈ P := by
    by_contra h
    exact (ntDoubleSwap_breaks_of_outside hj hab hbc hcd hq h) hnext
  have hpredP : pred ∈ P := by
    by_contra h
    apply (ntDoubleSwap_breaks_of_outside hj hab hbc hcd h ?_) hprev
    simpa only [pred, r, hrpred] using hq
  let B := ntBoundary P
  have hpredB : pred ∈ B := by
    apply (nt_mem_boundary_iff P pred).2
    rw [hrpred]
    exact ⟨fun _ => hq, fun _ => hpredP⟩
  have hqB : q ∈ B := by
    apply (nt_mem_boundary_iff P q).2
    exact ⟨fun h => False.elim (hq h), fun h => False.elim (h hrqP)⟩
  have hpredq : pred ≠ q := ntRotate_symm_ne_self (by omega) q
  have hpair : ({pred, q} : Finset (Fin n)) ⊆ B := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hpredB
    · exact hqB
  have hBsub : B ⊆ ntBreaks γ :=
    ntBoundary_subset_doubleSwap_breaks hj hab hbc hcd
  have hBle : B.card ≤ 3 := by
    calc
      B.card ≤ (ntBreaks γ).card := Finset.card_le_card hBsub
      _ = 3 := hcard
  have hBge : 2 ≤ B.card := by
    have h := Finset.card_le_card hpair
    simpa [hpredq] using h
  obtain ⟨t, ht⟩ := ntBoundary_card_even P
  change B.card = 2 * t at ht
  have hBcard : B.card = 2 := by omega
  have hpairCard : ({pred, q} : Finset (Fin n)).card = 2 := by simp [hpredq]
  have hBeq : B = {pred, q} := by
    exact (Finset.eq_of_subset_of_card_le hpair (by rw [hBcard, hpairCard])).symm
  let S := insert q P
  have hinv (i : Fin n) : i ∈ S ↔ r i ∈ S := by
    by_cases hiq : i = q
    · subst i
      simp [S, hrqP]
    by_cases hriq : r i = q
    · have hipred : i = pred := by
        apply r.injective
        rw [hriq, hrpred]
      have hiP : i ∈ P := by rwa [hipred]
      simp [S, hiq, hriq, hiP]
    · have hiB : i ∉ B := by
        rw [hBeq]
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        refine ⟨?_, hiq⟩
        intro hipred
        apply hriq
        rw [hipred, hrpred]
      have hiPiff : i ∈ P ↔ r i ∈ P := by
        by_cases hiP : i ∈ P
        · refine ⟨fun _ => ?_, fun _ => hiP⟩
          by_contra h
          apply hiB
          exact (nt_mem_boundary_iff P i).2 ⟨fun _ => h, fun _ => hiP⟩
        · refine ⟨fun h => False.elim (hiP h), fun hriP => ?_⟩
          exact False.elim (hiB ((nt_mem_boundary_iff P i).2
            ⟨fun h => False.elim (hiP h), fun h => False.elim (h hriP)⟩))
      simp only [S, Finset.mem_insert, hiq, hriq, false_or]
      exact hiPiff
  have hqS : q ∈ S := Finset.mem_insert_self q P
  have hiter : ∀ t : ℕ, (r^[t]) q ∈ S := by
    intro t
    induction t with
    | zero => simpa using hqS
    | succ t ih =>
        rw [Function.iterate_succ_apply']
        exact (hinv _).mp ih
  have hall : ∀ x : Fin n, x ∈ S := by
    intro x
    let z : Fin n := x - q
    have hx : (r^[z.val]) q = x := by
      rw [← finCycle_eq_finRotate_iterate (k := z)]
      simp [finCycle_apply, z]
    rw [← hx]
    exact hiter z.val
  have hSuniv : S = Finset.univ := Finset.eq_univ_of_forall hall
  have hPcard : P.card = 4 := by
    have hab' : a ≠ b := by intro h; subst b; omega
    have hac : a ≠ c := by intro h; subst c; omega
    have had : a ≠ d := by intro h; subst d; omega
    have hbc' : b ≠ c := by intro h; subst c; omega
    have hbd : b ≠ d := by intro h; subst d; omega
    have hcd' : c ≠ d := by intro h; subst d; omega
    simp [P, hab', hac, had, hbc', hbd, hcd']
  have hScard : S.card = 5 := by
    change (insert q P).card = 5
    rw [Finset.card_insert_of_notMem hq, hPcard]
  have huniv : S.card = n := by rw [hSuniv, Finset.card_univ, Fintype.card_fin]
  omega

private lemma ntK_delete_mem_DSemi {m : ℕ} {σ : Equiv.Perm (Fin (m + 1))}
    (o : ntOccurrence σ) {y : Fin (m + 1)} {ρ : Equiv.Perm (Fin m)}
    (hσρ : σ = ntIns y (σ y) ρ) (hy : y ∉ o.positions)
    {j : ℕ} {hj : j + 1 ≤ m} (hK : ρ ∈ ntK m j hj) :
    y ∈ ntDSemi (σ * Equiv.swap o.a o.c) ∪
      ntDSemi (σ * Equiv.swap o.b o.d) := by
  obtain ⟨o', ha, hb, hc, hd⟩ := ntOccurrence_delete_data o hσρ hy
  obtain ⟨⟨P, Q, hPQ, hρ⟩, -⟩ := hK
  have hocc := ntBeta_occur hj hPQ hρ o'.hab o'.hbc o'.hcd o'.hpat
  rcases hocc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · apply Finset.mem_union.mpr
    left
    simpa only [ha, hc] using
      nt_mem_DSemi_unswap hj y (σ y) o'.a o'.c (hσρ.trans (congrArg (ntIns y (σ y)) hρ))
  · apply Finset.mem_union.mpr
    left
    rw [Equiv.swap_comm]
    simpa only [ha, hc] using
      nt_mem_DSemi_unswap hj y (σ y) o'.c o'.a (hσρ.trans (congrArg (ntIns y (σ y)) hρ))
  · apply Finset.mem_union.mpr
    right
    simpa only [hb, hd] using
      nt_mem_DSemi_unswap hj y (σ y) o'.b o'.d (hσρ.trans (congrArg (ntIns y (σ y)) hρ))
  · apply Finset.mem_union.mpr
    right
    rw [Equiv.swap_comm]
    simpa only [hb, hd] using
      nt_mem_DSemi_unswap hj y (σ y) o'.d o'.b (hσρ.trans (congrArg (ntIns y (σ y)) hρ))

private lemma ntDSemi_sdiff_not_both {k : ℕ} (hk : 6 ≤ k)
    {σ : Equiv.Perm (Fin (k + 2))} (o : ntOccurrence σ)
    (hα₂ : ¬ntSemi (σ * Equiv.swap o.b o.d)) :
    ntDSemi (σ * Equiv.swap o.a o.c) \ o.positions = ∅ ∨
      ntDSemi (σ * Equiv.swap o.b o.d) \ o.positions = ∅ := by
  classical
  by_contra hboth
  simp only [not_or] at hboth
  have hD₁ne : (ntDSemi (σ * Equiv.swap o.a o.c) \ o.positions).Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr hboth.1
  have hD₂ne : (ntDSemi (σ * Equiv.swap o.b o.d) \ o.positions).Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr hboth.2
  obtain ⟨y₁, hy₁mem⟩ := hD₁ne
  have hy₁ := Finset.mem_sdiff.mp hy₁mem
  have hy₁D := hy₁.1
  have hy₁P := hy₁.2
  obtain ⟨y₂, hy₂mem⟩ := hD₂ne
  have hy₂ := Finset.mem_sdiff.mp hy₂mem
  have hy₂D := hy₂.1
  have hy₂P := hy₂.2
  obtain ⟨ρσ, hσρ⟩ := ntIns_exists y₁ (σ y₁) σ rfl
  obtain ⟨o', ha, hb, hc, hd⟩ := ntOccurrence_delete_data o hσρ hy₁P
  obtain ⟨β, hα₁ins, hβsemi⟩ :=
    (nt_mem_DSemi_iff (σ * Equiv.swap o.a o.c) y₁).1 hy₁D
  obtain ⟨j, hj, hβ⟩ := hβsemi
  let γ := ntBeta (k + 1) j hj *
    (Equiv.swap o'.a o'.c * Equiv.swap o'.b o'.d)
  have hrel : σ * Equiv.swap o.b o.d =
      (σ * Equiv.swap o.a o.c) * Equiv.swap o.a o.c * Equiv.swap o.b o.d := by
    rw [mul_assoc σ (Equiv.swap o.a o.c) (Equiv.swap o.a o.c),
      Equiv.swap_mul_self, mul_one]
  have hAC : ntIns y₁ ((σ * Equiv.swap o.a o.c) y₁) β * Equiv.swap o.a o.c =
      ntIns y₁ ((σ * Equiv.swap o.a o.c) y₁) (β * Equiv.swap o'.a o'.c) := by
    rw [← ha, ← hc, ← ntIns_mul_swap]
  have hBD : ntIns y₁ ((σ * Equiv.swap o.a o.c) y₁)
      (β * Equiv.swap o'.a o'.c) * Equiv.swap o.b o.d =
      ntIns y₁ ((σ * Equiv.swap o.a o.c) y₁)
        ((β * Equiv.swap o'.a o'.c) * Equiv.swap o'.b o'.d) := by
    rw [← hb, ← hd, ← ntIns_mul_swap]
  have hα₂ins : σ * Equiv.swap o.b o.d =
      ntIns y₁ ((σ * Equiv.swap o.a o.c) y₁) γ := by
    calc
      σ * Equiv.swap o.b o.d =
          (σ * Equiv.swap o.a o.c) * Equiv.swap o.a o.c * Equiv.swap o.b o.d := hrel
      _ = ntIns y₁ ((σ * Equiv.swap o.a o.c) y₁) β *
          Equiv.swap o.a o.c * Equiv.swap o.b o.d :=
        congrArg (fun τ => τ * Equiv.swap o.a o.c * Equiv.swap o.b o.d) hα₁ins
      _ = ntIns y₁ ((σ * Equiv.swap o.a o.c) y₁)
          (β * Equiv.swap o'.a o'.c) * Equiv.swap o.b o.d := by
        rw [hAC]
      _ = ntIns y₁ ((σ * Equiv.swap o.a o.c) y₁)
          ((β * Equiv.swap o'.a o'.c) * Equiv.swap o'.b o'.d) := by
        exact hBD
      _ = ntIns y₁ ((σ * Equiv.swap o.a o.c) y₁) γ := by
        rw [hβ]
        rfl
  have hα₂card : (ntBreaks (σ * Equiv.swap o.b o.d)).card = 3 :=
    ntBreaks_card_eq_three_of_mem_DSemi (by omega) hα₂ hy₂D
  have hγle : (ntBreaks γ).card ≤ 3 := by
    have h := ntBreaks_delete_card_le (by omega) y₁
      ((σ * Equiv.swap o.a o.c) y₁) γ
    rw [← hα₂ins, hα₂card] at h
    exact h
  have hγge : 3 ≤ (ntBreaks γ).card := by
    change 3 ≤ (ntBreaks (ntBeta (k + 1) j hj *
      (Equiv.swap o'.a o'.c * Equiv.swap o'.b o'.d))).card
    exact ntDoubleSwap_breaks_card_ge_three (by omega) hj o'.hab o'.hbc o'.hcd
  have hγcard : (ntBreaks γ).card = 3 := by omega
  let f := ntBreakMap y₁ ((σ * Equiv.swap o.a o.c) y₁) γ
  let I := (ntBreaks γ).image f
  have hImaps : I ⊆ ntBreaks (σ * Equiv.swap o.b o.d) := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    change ntBreakMap y₁ ((σ * Equiv.swap o.a o.c) y₁) γ z ∈ _
    rw [hα₂ins]
    exact ntBreakMap_mem (by omega) y₁ ((σ * Equiv.swap o.a o.c) y₁) γ hz
  have hfinj : (ntBreaks γ : Set (Fin (k + 1))).InjOn f :=
    ntBreakMap_injOn y₁ ((σ * Equiv.swap o.a o.c) y₁) γ
  have hIcard : I.card = 3 := by
    change ((ntBreaks γ).image f).card = 3
    rw [Finset.card_image_of_injOn hfinj, hγcard]
  have hIeq : I = ntBreaks (σ * Equiv.swap o.b o.d) :=
    Finset.eq_of_subset_of_card_le hImaps (by rw [hα₂card, hIcard])
  have hpre {x : Fin (k + 2)} (hx : x ∈ ntBreaks (σ * Equiv.swap o.b o.d)) :
      ∃ z ∈ ntBreaks γ, f z = x := by
    have hxI : x ∈ I := by rw [hIeq]; exact hx
    exact Finset.mem_image.mp hxI
  have hy₂pair := ntDSemi_pair_mem (by omega) hα₂ hy₂D
  let pred₂ := (finRotate (k + 2)).symm y₂
  have hpred₂ : pred₂ ∈ ntBreaks (σ * Equiv.swap o.b o.d) := hy₂pair.1
  have hy₂break : y₂ ∈ ntBreaks (σ * Equiv.swap o.b o.d) := hy₂pair.2
  by_cases hy₁₂ : y₁ = y₂
  · subst y₂
    obtain ⟨z, hz, hfz⟩ := hpre hy₂break
    change ntBreakMap y₁ ((σ * Equiv.swap o.a o.c) y₁) γ z = y₁ at hfz
    have hcross : finRotate (k + 2) (y₁.succAbove z) = y₁ := by
      exact ntBreakMap_cross_of_eq y₁ ((σ * Equiv.swap o.a o.c) y₁) γ z hfz
    have hw : y₁.succAbove z = pred₂ := by
      apply (finRotate (k + 2)).injective
      rw [hcross, (finRotate (k + 2)).apply_symm_apply]
    have hpredIns : pred₂ ∈
        ntBreaks (ntIns y₁ ((σ * Equiv.swap o.a o.c) y₁) γ) := by
      rw [← hα₂ins]
      exact hpred₂
    have hfprev : f z = pred₂ := by
      unfold f ntBreakMap
      dsimp only
      rw [ite_eq_left hcross, ite_eq_left (by simpa only [hw] using hpredIns), hw]
    have hne : pred₂ ≠ y₁ := by
      change (finRotate (k + 2)).symm y₁ ≠ y₁
      exact ntRotate_symm_ne_self (by omega) y₁
    exact hne (hfprev.symm.trans hfz)
  · obtain ⟨q, hq⟩ := Fin.exists_succAbove_eq (Ne.symm hy₁₂)
    have hqP : q ∉ o'.positions := by
      intro h
      simp only [ntOccurrence.positions, Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with rfl | rfl | rfl | rfl
      · apply hy₂P
        rw [← hq, ha]
        simp [ntOccurrence.positions]
      · apply hy₂P
        rw [← hq, hb]
        simp [ntOccurrence.positions]
      · apply hy₂P
        rw [← hq, hc]
        simp [ntOccurrence.positions]
      · apply hy₂P
        rw [← hq, hd]
        simp [ntOccurrence.positions]
    obtain ⟨z₂, hz₂, hfz₂⟩ := hpre hy₂break
    change ntBreakMap y₁ ((σ * Equiv.swap o.a o.c) y₁) γ z₂ = y₂ at hfz₂
    have hfz₂not : ntBreakMap y₁ ((σ * Equiv.swap o.a o.c) y₁) γ z₂ ≠ y₁ := by
      rw [hfz₂]
      exact Ne.symm hy₁₂
    have hwz₂ : y₁.succAbove z₂ = y₂ := by
      have h := ntBreakMap_eq_succAbove_of_ne y₁
        ((σ * Equiv.swap o.a o.c) y₁) γ z₂ hfz₂not
      rw [hfz₂] at h
      exact h.symm
    have hz₂q : z₂ = q := Fin.succAbove_right_injective (hwz₂.trans hq.symm)
    have hqbreak : q ∈ ntBreaks γ := by rwa [← hz₂q]
    obtain ⟨z₁, hz₁, hfz₁⟩ := hpre hpred₂
    change ntBreakMap y₁ ((σ * Equiv.swap o.a o.c) y₁) γ z₁ = pred₂ at hfz₁
    have hrot : finRotate (k + 1) z₁ = q := by
      by_cases hp : pred₂ = y₁
      · have hcross : finRotate (k + 2) (y₁.succAbove z₁) = y₁ := by
          apply ntBreakMap_cross_of_eq y₁ ((σ * Equiv.swap o.a o.c) y₁) γ z₁
          rw [hfz₁, hp]
        have hpos := ntRotate_succAbove_cross (by omega) y₁ z₁ hcross
        apply Fin.succAbove_right_injective
        rw [hpos, hq]
        change finRotate (k + 2) y₁ = y₂
        rw [← hp]
        exact (finRotate (k + 2)).apply_symm_apply y₂
      · have hfz₁not : ntBreakMap y₁ ((σ * Equiv.swap o.a o.c) y₁) γ z₁ ≠ y₁ := by
          rw [hfz₁]
          exact hp
        have hwz₁ : y₁.succAbove z₁ = pred₂ := by
          have h := ntBreakMap_eq_succAbove_of_ne y₁
            ((σ * Equiv.swap o.a o.c) y₁) γ z₁ hfz₁not
          rw [hfz₁] at h
          exact h.symm
        have hcross : finRotate (k + 2) (y₁.succAbove z₁) ≠ y₁ := by
          rw [hwz₁, (finRotate (k + 2)).apply_symm_apply]
          exact Ne.symm hy₁₂
        have hpos := ntRotate_succAbove (by omega) y₁ z₁ hcross
        apply Fin.succAbove_right_injective
        rw [← hpos, hwz₁, (finRotate (k + 2)).apply_symm_apply, hq]
    have hz₁prev : z₁ = (finRotate (k + 1)).symm q := by
      apply (finRotate (k + 1)).injective
      rw [hrot, (finRotate (k + 1)).apply_symm_apply]
    have hfive : k + 1 = 5 := by
      apply ntDoubleSwap_three_shared_outside (by omega) hj o'.hab o'.hbc o'.hcd
      · exact hγcard
      · exact hqP
      · rwa [← hz₁prev]
      · exact hqbreak
    omega

private def ntStartBad {k : ℕ} (σ : Equiv.Perm (Fin (k + 2))) :
    Finset (Fin (k + 2)) :=
  (if σ 1 = Fin.last (k + 1) then {0} else ∅) ∪
    (if σ 0 = (⟨k, by omega⟩ : Fin (k + 2))
      then {σ.symm (Fin.last (k + 1))} else ∅)

private def ntEndBad {k : ℕ} (σ : Equiv.Perm (Fin (k + 2))) :
    Finset (Fin (k + 2)) :=
  (if σ (⟨k, by omega⟩ : Fin (k + 2)) = 0
      then {Fin.last (k + 1)} else ∅) ∪
    (if σ (Fin.last (k + 1)) = 1 then {σ.symm 0} else ∅)

private def ntEBad {k : ℕ} (σ : Equiv.Perm (Fin (k + 2))) :
    Finset (Fin (k + 2)) := ntStartBad σ ∪ ntEndBad σ

private lemma ntDeletion_large {k : ℕ} (hk : 7 ≤ k)
    {σ : Equiv.Perm (Fin (k + 2))} (hσ : σ ∈ ntG (k + 1)) :
    ∃ y : Fin (k + 2), ∃ ρ ∈ ntG k, σ = ntIns y (σ y) ρ := by
  classical
  obtain ⟨o, htop, hbottom⟩ := ntChoose_occurrence (by omega) hσ.1 hσ.2.1
  let α₁ := σ * Equiv.swap o.a o.c
  let α₂ := σ * Equiv.swap o.b o.d
  have hac : o.a ≠ o.c := by
    intro h
    have hv := congrArg Fin.val h
    have hab := o.hab
    have hbc := o.hbc
    omega
  have hbd : o.b ≠ o.d := by
    intro h
    have hv := congrArg Fin.val h
    have hbc := o.hbc
    have hcd := o.hcd
    omega
  have hα₁ : ¬ntSemi α₁ := ntUnswap_not_semi hσ.2.1 hσ.2.2 hac
  have hα₂ : ¬ntSemi α₂ := ntUnswap_not_semi hσ.2.1 hσ.2.2 hbd
  have hD₁ : (ntDSemi α₁ \ o.positions).card ≤ 2 := by
    exact le_trans (Finset.card_le_card Finset.sdiff_subset)
      (ntDSemi_card_le_two (by omega) hα₁)
  have hD₂ : (ntDSemi α₂ \ o.positions).card ≤ 2 := by
    exact le_trans (Finset.card_le_card Finset.sdiff_subset)
      (ntDSemi_card_le_two (by omega) hα₂)
  have hDone : ntDSemi α₁ \ o.positions = ∅ ∨
      ntDSemi α₂ \ o.positions = ∅ := by
    exact ntDSemi_sdiff_not_both (by omega) o hα₂
  have hTbad : ((ntDSemi α₁ \ o.positions) ∪
      (ntDSemi α₂ \ o.positions)).card ≤ 2 := by
    rcases hDone with h | h
    · simp [h, hD₂]
    · simp [h, hD₁]
  have hEbad : (ntEBad σ \ o.positions).card ≤ 2 :=
    ntEBad_sdiff_card o htop hbottom
  let bad := (ntEBad σ \ o.positions) ∪
    ((ntDSemi α₁ \ o.positions) ∪ (ntDSemi α₂ \ o.positions))
  have hbad : bad.card ≤ 4 := by
    calc
      bad.card ≤ (ntEBad σ \ o.positions).card +
          ((ntDSemi α₁ \ o.positions) ∪
            (ntDSemi α₂ \ o.positions)).card := Finset.card_union_le _ _
      _ ≤ 4 := by omega
  let available := Finset.univ \ o.positions
  have hpositions : o.positions ⊆ (Finset.univ : Finset (Fin (k + 2))) :=
    fun _ _ => Finset.mem_univ _
  have havailable : available.card = k - 2 := by
    rw [Finset.card_sdiff_of_subset hpositions, Finset.card_univ,
      Fintype.card_fin, ntOccurrence_positions_card]
    omega
  have hnsub : ¬available ⊆ bad := by
    intro hsub
    have hcard := Finset.card_le_card hsub
    rw [havailable] at hcard
    omega
  obtain ⟨y, hyavailable, hybad⟩ := Finset.not_subset.mp hnsub
  have hypos : y ∉ o.positions := (Finset.mem_sdiff.mp hyavailable).2
  obtain ⟨ρ, hσρ⟩ := ntIns_exists y (σ y) σ rfl
  refine ⟨y, ρ, ?_, hσρ⟩
  refine ⟨?_, ntOccurrence_delete o hσρ hypos, ?_⟩
  · apply ntDeletion_memE_of_not_bad hσ.1 hσρ
    intro hyE
    apply hybad
    simp only [bad, Finset.mem_union]
    exact Or.inl (Finset.mem_sdiff.mpr ⟨hyE, hypos⟩)
  · intro j hj hK
    have hyD := ntK_delete_mem_DSemi o hσρ hypos hK
    apply hybad
    simp only [bad, Finset.mem_union]
    rcases Finset.mem_union.mp hyD with hyD | hyD
    · exact Or.inr (Or.inl (Finset.mem_sdiff.mpr ⟨hyD, hypos⟩))
    · exact Or.inr (Or.inr (Finset.mem_sdiff.mpr ⟨hyD, hypos⟩))

/-- Insertion step: non-inert insertions land in a reference class. -/
private lemma ntInsertion {m : ℕ} (hm : 5 ≤ m)
    (hIH : ∀ ρ ∈ ntG (m + 1),
      Relation.EqvGen (ntMove (m + 2)) ρ (ntEven (m + 2)) ∨
        Relation.EqvGen (ntMove (m + 2)) ρ (ntOdd m))
    {y v : Fin (m + 3)} {ρ : Equiv.Perm (Fin (m + 2))}
    (hρ : ρ ∈ ntG (m + 1))
    (hyv : (y ≠ 0 ∨ v ≠ Fin.last (m + 2)) ∧
      (y ≠ Fin.last (m + 2) ∨ v ≠ 0)) :
    Relation.EqvGen (ntMove (m + 3)) (ntIns y v ρ) (ntEven (m + 3)) ∨
      Relation.EqvGen (ntMove (m + 3)) (ntIns y v ρ) (ntOdd (m + 1)) := by
  by_cases hp1 : (y.val, v.val) = (1, m + 2)
  · have hy : y = (⟨1, by omega⟩ : Fin (m + 3)) := by
      apply Fin.ext
      exact congrArg Prod.fst hp1
    have hv : v = (⟨m + 2, by omega⟩ : Fin (m + 3)) := by
      apply Fin.ext
      exact congrArg Prod.snd hp1
    rw [hy, hv]
    exact ntInsertion_pair1 hm hIH hρ
  by_cases hp2 : (y.val, v.val) = (m + 1, 0)
  · have hy : y = (⟨m + 1, by omega⟩ : Fin (m + 3)) := by
      apply Fin.ext
      exact congrArg Prod.fst hp2
    have hv : v = (⟨0, by omega⟩ : Fin (m + 3)) := by
      apply Fin.ext
      exact congrArg Prod.snd hp2
    rw [hy, hv]
    exact ntInsertion_pair2 hm hIH hρ
  by_cases hp3 : (y.val, v.val) = (m + 2, 1)
  · have hy : y = (⟨m + 2, by omega⟩ : Fin (m + 3)) := by
      apply Fin.ext
      exact congrArg Prod.fst hp3
    have hv : v = (⟨1, by omega⟩ : Fin (m + 3)) := by
      apply Fin.ext
      exact congrArg Prod.snd hp3
    rw [hy, hv]
    exact ntInsertion_pair3 hm hIH hρ
  by_cases hp4 : (y.val, v.val) = (0, m + 1)
  · have hy : y = (⟨0, by omega⟩ : Fin (m + 3)) := by
      apply Fin.ext
      exact congrArg Prod.fst hp4
    have hv : v = (⟨m + 1, by omega⟩ : Fin (m + 3)) := by
      apply Fin.ext
      exact congrArg Prod.snd hp4
    rw [hy, hv]
    exact ntInsertion_pair4 hm hIH hρ
  by_cases hb : 1 ≤ y.val ∧ 1 ≤ v.val
  · exact ntIns_branch1 hm hIH hρ hb.1 hb.2 hp1 hp3
  · have hc1 : y.val ≠ 0 ∨ v.val ≠ m + 2 := by
      rcases hyv.1 with hy | hv
      · exact Or.inl (fun h => hy (Fin.ext h))
      · exact Or.inr (fun h => hv (Fin.ext (by simpa using h)))
    have hc2 : y.val ≠ m + 2 ∨ v.val ≠ 0 := by
      rcases hyv.2 with hy | hv
      · exact Or.inl (fun h => hy (Fin.ext (by simpa using h)))
      · exact Or.inr (fun h => hv (Fin.ext h))
    have hb' : y.val < 1 ∨ v.val < 1 := by omega
    have hyU : y.val ≤ m + 1 := by
      rcases hb' with hy0 | hv0
      · omega
      · rcases hc2 with hyL | hvZ
        · omega
        · omega
    have hvU : v.val ≤ m + 1 := by
      rcases hb' with hy0 | hv0
      · rcases hc1 with hyZ | hvL
        · omega
        · omega
      · omega
    exact ntIns_branch2 hm hIH hρ hyU hvU hp4 hp2

private def ntCode {n : ℕ} (σ : Equiv.Perm (Fin n)) : List ℕ :=
  List.ofFn fun i => (σ i).val

private lemma ntExists_perm_code {n : ℕ} {s : List ℕ}
    (hs : s ∈ List.permutations' (List.range n)) :
    ∃ σ : Equiv.Perm (Fin n), ntCode σ = s := by
  have hp : s.Perm (List.range n) := List.mem_permutations'.mp hs
  have hlen : s.length = n := by simpa using hp.length_eq
  have hnodup : s.Nodup := hp.nodup_iff.mpr List.nodup_range
  let idx : Fin n → Fin s.length := fun i => ⟨i.val, by rw [hlen]; exact i.is_lt⟩
  let f : Fin n → Fin n := fun i =>
    ⟨s.get (idx i), List.mem_range.mp (hp.mem_iff.mp (s.get_mem (idx i)))⟩
  have hinj : Function.Injective f := by
    intro i j hij
    have hget : s.get (idx i) = s.get (idx j) := congrArg Fin.val hij
    have hidx : idx i = idx j := hnodup.get_inj_iff.mp hget
    apply Fin.ext
    simpa only [idx] using congrArg Fin.val hidx
  let σ : Equiv.Perm (Fin n) := Equiv.ofBijective f
    (Finite.injective_iff_bijective.mp hinj)
  refine ⟨σ, ?_⟩
  apply List.ext_getElem
  · simpa [ntCode] using hlen.symm
  · intro i hiCode hiS
    have hi : i < n := by simpa [ntCode] using hiCode
    simp only [ntCode, List.getElem_ofFn]
    change (f ⟨i, hi⟩).val = s[i]
    rfl

private noncomputable def ntPermOfCode {n : ℕ} (s : List ℕ)
    (hs : s ∈ List.permutations' (List.range n)) : Equiv.Perm (Fin n) :=
  Classical.choose (ntExists_perm_code hs)

private lemma ntCode_permOfCode {n : ℕ} (s : List ℕ)
    (hs : s ∈ List.permutations' (List.range n)) :
    ntCode (ntPermOfCode s hs) = s :=
  Classical.choose_spec (ntExists_perm_code hs)

private def ntQuads (n : ℕ) : List (ℕ × ℕ × ℕ × ℕ) :=
  (List.range n).flatMap fun a => (List.range n).flatMap fun b =>
    (List.range n).flatMap fun c => (List.range n).filterMap fun d =>
      if a < b ∧ b < c ∧ c < d then some (a, b, c, d) else none

private def ntHasPatB (q : List (ℕ × ℕ × ℕ × ℕ)) (s : List ℕ) : Bool :=
  q.any fun (a, b, c, d) =>
    let x := s.getD a 0
    let y := s.getD b 0
    let z := s.getD c 0
    let w := s.getD d 0
    (x < y && y < z && z < w) || (z < w && w < x && x < y)

private def ntSemiVal (n j i : ℕ) : ℕ :=
  (j + n - 1 - i) % n

private def ntInTB (n : ℕ) (s : List ℕ) : Bool :=
  (List.range n).any fun j => (List.range n).any fun p =>
    (List.range n).any fun q => p != q && (List.range n).all fun i =>
      s.getD i 0 == if i = p then ntSemiVal n j q
        else if i = q then ntSemiVal n j p else ntSemiVal n j i

private def ntIsGB (n : ℕ) (q : List (ℕ × ℕ × ℕ × ℕ)) (s : List ℕ) : Bool :=
  s.headD 0 != n - 1 && s.getLastD 0 != 0 && ntHasPatB q s && !ntInTB n s

private def ntNbrAt (s : List ℕ) (q : ℕ × ℕ × ℕ × ℕ) : Option (List ℕ) :=
  let (a, b, c, d) := q
  let x := s.getD a 0
  let y := s.getD b 0
  let z := s.getD c 0
  let w := s.getD d 0
  if (x < y && y < z && z < w) || (z < w && w < x && x < y) then
    some (((((s.set a z).set c x).set b w).set d y))
  else none

private def ntNbrs (q : List (ℕ × ℕ × ℕ × ℕ)) (s : List ℕ) : List (List ℕ) :=
  q.filterMap (ntNbrAt s)

private def ntFact : ℕ → ℕ
  | 0 => 1
  | k + 1 => (k + 1) * ntFact k

private def ntLehmer : List ℕ → ℕ
  | [] => 0
  | x :: xs => (xs.countP (· < x)) * ntFact xs.length + ntLehmer xs

private lemma ntSemiVal_eq_beta {n j i : ℕ} (hj : j + 1 ≤ n) (hi : i < n) :
    ntSemiVal n j i = ((ntBeta n j hj) ⟨i, hi⟩).val := by
  rw [ntBeta_val]
  unfold ntSemiVal
  by_cases hij : i < j
  · rw [ite_eq_left hij]
    have heq : j + n - 1 - i = n + (j - 1 - i) := by omega
    have ha : j - 1 - i < n := by omega
    rw [heq, Nat.add_mod]
    simp only [Nat.mod_self, zero_add, Nat.mod_eq_of_lt ha]
  · rw [ite_eq_right hij]
    have hlt : j + n - 1 - i < n := by omega
    rw [Nat.mod_eq_of_lt hlt]
    change j + n - 1 - i = n + j - 1 - i
    omega

private lemma ntInTB_sound {n : ℕ} {σ : Equiv.Perm (Fin n)}
    (h : ntInTB n (ntCode σ) = true) :
    ∃ j : ℕ, ∃ hj : j + 1 ≤ n, σ ∈ ntT n j hj := by
  unfold ntInTB at h
  rw [List.any_eq_true] at h
  obtain ⟨j, hjmem, h⟩ := h
  rw [List.any_eq_true] at h
  obtain ⟨p, hpmem, h⟩ := h
  rw [List.any_eq_true] at h
  obtain ⟨q, hqmem, h⟩ := h
  rw [Bool.and_eq_true] at h
  obtain ⟨hpq, hall⟩ := h
  have hjlt := List.mem_range.mp hjmem
  have hplt := List.mem_range.mp hpmem
  have hqlt := List.mem_range.mp hqmem
  have hjn : j + 1 ≤ n := by omega
  have hpq' : p ≠ q := by
    intro heq
    subst q
    simp at hpq
  let P : Fin n := ⟨p, hplt⟩
  let Q : Fin n := ⟨q, hqlt⟩
  have hPQ : P ≠ Q := by
    intro heq
    exact hpq' (congrArg Fin.val heq)
  refine ⟨j, hjn, P, Q, hPQ, ?_⟩
  apply Equiv.Perm.ext
  intro i
  apply Fin.ext
  rw [Equiv.Perm.mul_apply]
  by_cases hiP : i = P
  · subst i
    rw [Equiv.swap_apply_left]
    have heq := (List.all_eq_true.mp hall) p hpmem
    rw [beq_iff_eq] at heq
    rw [ntCode_getD σ p hplt, ite_eq_left rfl,
      ntSemiVal_eq_beta hjn hqlt] at heq
    exact heq
  · by_cases hiQ : i = Q
    · subst i
      rw [Equiv.swap_apply_right]
      have heq := (List.all_eq_true.mp hall) q hqmem
      rw [beq_iff_eq] at heq
      have hqp : q ≠ p := Ne.symm hpq'
      rw [ntCode_getD σ q hqlt, ite_eq_right hqp, ite_eq_left rfl,
        ntSemiVal_eq_beta hjn hplt] at heq
      exact heq
    · rw [Equiv.swap_apply_of_ne_of_ne hiP hiQ]
      have heq := (List.all_eq_true.mp hall) i.val
        (List.mem_range.mpr i.is_lt)
      rw [beq_iff_eq] at heq
      have hip : i.val ≠ p := fun heq' => hiP (Fin.ext heq')
      have hiq : i.val ≠ q := fun heq' => hiQ (Fin.ext heq')
      rw [ntCode_getD σ i.val i.is_lt, ite_eq_right hip, ite_eq_right hiq,
        ntSemiVal_eq_beta hjn i.is_lt] at heq
      exact heq

private lemma ntIsGB_of_memG7 {σ : Equiv.Perm (Fin 7)} (hσ : σ ∈ ntG 6) :
    ntIsGB 7 (ntQuads 7) (ntCode σ) = true := by
  simp only [ntIsGB, Bool.and_eq_true, Bool.not_eq_true']
  refine ⟨⟨⟨?_, ?_⟩, ntHasPatB_of_pat hσ.2.1⟩, ?_⟩
  · apply bne_iff_ne.mpr
    simp only [ntCode, List.ofFn_succ, List.headD_cons]
    intro heq
    apply hσ.1.1
    apply Fin.ext
    simpa using heq
  · apply bne_iff_ne.mpr
    simp only [ntCode]
    rw [show (List.ofFn fun i : Fin 7 => (σ i).val).getLastD 0 =
      (σ (Fin.last 6)).val by simp [List.ofFn_succ]]
    intro heq
    apply hσ.1.2
    apply Fin.ext
    exact heq
  · apply Bool.eq_false_iff.mpr
    intro hT
    obtain ⟨j, hj, hσT⟩ := ntInTB_sound hT
    exact hσ.2.2 j hj ⟨hσT, hσ.2.1⟩

private lemma ntIsGB_of_memG8 {σ : Equiv.Perm (Fin 8)} (hσ : σ ∈ ntG 7) :
    ntIsGB 8 (ntQuads 8) (ntCode σ) = true := by
  simp only [ntIsGB, Bool.and_eq_true, Bool.not_eq_true']
  refine ⟨⟨⟨?_, ?_⟩, ntHasPatB_of_pat hσ.2.1⟩, ?_⟩
  · apply bne_iff_ne.mpr
    simp only [ntCode, List.ofFn_succ, List.headD_cons]
    intro heq
    apply hσ.1.1
    apply Fin.ext
    simpa using heq
  · apply bne_iff_ne.mpr
    simp only [ntCode]
    rw [show (List.ofFn fun i : Fin 8 => (σ i).val).getLastD 0 =
      (σ (Fin.last 7)).val by simp [List.ofFn_succ]]
    intro heq
    apply hσ.1.2
    apply Fin.ext
    exact heq
  · apply Bool.eq_false_iff.mpr
    intro hT
    obtain ⟨j, hj, hσT⟩ := ntInTB_sound hT
    exact hσ.2.2 j hj ⟨hσT, hσ.2.1⟩

private def ntRepCodes5 : List (List ℕ) :=
  [[0, 1, 2, 3, 4], [0, 1, 2, 4, 3], [0, 1, 3, 2, 4],
    [0, 1, 3, 4, 2], [0, 1, 4, 2, 3], [0, 2, 1, 3, 4],
    [1, 0, 2, 3, 4], [1, 2, 3, 4, 0], [4, 0, 1, 2, 3]]

private def ntRepCodes6 : List (List ℕ) :=
  [[0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 5, 4], [0, 1, 2, 4, 5, 3],
    [0, 1, 2, 5, 4, 3], [0, 1, 4, 3, 2, 5], [0, 1, 5, 3, 4, 2],
    [0, 2, 1, 3, 5, 4], [0, 3, 2, 1, 4, 5], [1, 0, 2, 4, 3, 5],
    [1, 2, 3, 4, 5, 0], [1, 2, 3, 5, 4, 0], [1, 2, 4, 3, 5, 0],
    [1, 2, 4, 5, 3, 0], [1, 2, 5, 3, 4, 0], [1, 3, 2, 4, 5, 0],
    [2, 1, 3, 4, 5, 0], [2, 3, 4, 5, 1, 0], [5, 0, 1, 2, 3, 4],
    [5, 0, 1, 2, 4, 3], [5, 0, 1, 3, 2, 4], [5, 0, 1, 3, 4, 2],
    [5, 0, 1, 4, 2, 3], [5, 0, 2, 1, 3, 4], [5, 1, 0, 2, 3, 4],
    [5, 1, 2, 3, 4, 0], [5, 4, 0, 1, 2, 3]]

private def ntJoin64 (chunks : List ℕ) : ℕ :=
  chunks.foldl (fun acc chunk => (acc <<< 64) + chunk) 0

private def ntL5 : ℕ :=
  ntJoin64 [
    0xfffffff8,
    0xfffffffffffffff8,
    0xf07523f5fffff0ff,
    0xfff6fff5f2ff01f4,
    0xff10fffffffffff4,
    0xfffffff6ffffff75,
    0xf3fffff6fffff2f0,
    0xfff4ff23f5f43210,
  ]

private def ntD5 : ℕ :=
  ntJoin64 [
    0xfffffff1,
    0xfffffffffffffff0,
    0xf11111f1fffff1ff,
    0xfff1fff2f1ff11f1,
    0xff11fffffffffff2,
    0xfffffff1ffffff02,
    0xf2fffff0fffff2f1,
    0xfff2ff22f0f00000,
  ]

private def ntL6 : ℕ :=
  ntJoin64 [
    0xffff,
    0xfffff9ffffffffff,
    0xfffffffff9fc7169,
    0xd3f6ffffffc7ffff,
    0xff7ffff6fcfff8cb,
    0xf5ffe51fffffffff,
    0xfffff5fffffffff7,
    0xffffffff16fd3fff,
    0xfff7ffffffcff1ff,
    0xff5ffe74fdbf5a4e,
    0x51f85221060071c2,
    0x2585821048210420,
    0xf89c708be7ffffff,
    0x8bfffffe1fffe7f8,
    0x522107e2ffc22f87,
    0xfffffe2fffe2f81e,
    0x108be1ffffff81c7,
    0xf8be3fffe1f84224,
    0x07e2fffe2f8422f9,
    0xfe210422f896120b,
    0xe1ffc01489410984,
    0x108841f85a2117e2,
    0xffc2050522304221,
    0x0422f8bff09be1ff,
    0xcc1fffffffffffff,
    0xe1f87ff007e2ffc2,
    0x0ffda2f97fffffe2,
    0xfa3ff08be1ffc41f,
    0xfc45f8be1288c1f9,
    0x3ff107e2ffc22fff,
    0xffffc2200462f89e,
    0x108be1ffc41f8bff,
    0xffc4308041f87ff1,
    0x060071c22ffd82f8,
    0x46210420ffffffff,
    0xe3fffffffde1f8bf,
    0xffffe3ffffff87e2,
    0xfffe0ffc22f87e01,
    0x0422ffffffffe1ff,
    0xfffffd61f8bfffff,
    0xe1f8522407e2ffff,
    0xff85a2f97e2fffe2,
    0xfa3ff0896160841f,
    0xfdc7f8bff083e1ff,
    0xda2f958258422505,
    0x22307e200422ffff,
    0xffa3e1fffe1ffd01,
    0xf8be10a041ffffff,
    0x93e2fffe2ffc82f8,
    0x7e211022f804108b,
    0xe1fffe1f8045f8be,
    0x128841f87ff00482,
    0x10420ffc22f9fe01,
    0x0422ffc45f884120,
    0x8010884108be1088,
    0xc1f84a2104201102,
    0x2104221046210420,
  ]

private def ntD6 : ℕ :=
  ntJoin64 [
    0xfffffff1ffffffff,
    0xfffffff0f11111f1,
    0xfffff1fffff1fff2,
    0xf1ff11f1ff11ffff,
    0xfffffff2fffffff1,
    0xffffff02f2fffff0,
    0xfffff2f1fff2ff22,
    0xf0f00000f8133611,
    0x1161161454152922,
    0xf41143f1fffff4ff,
    0xfff9fff2f61356f3,
    0xff86f8fffff5fff4,
    0xf11861f8fffff122,
    0xf4f3fff9f76517f6,
    0xfff4f754f2f44575,
    0xf41417f6ff111518,
    0x81348737f61641f4,
    0xff11161518955663,
    0xf6ff81f4ff18ffff,
    0xfffffff5f6ff11f4,
    0xff11ff27f2fffff5,
    0xf1ff77f8ff85ff52,
    0xf5f52527f1ff49f3,
    0xff86ffffff811114,
    0xf21943f9ff56f4ff,
    0xff611118f2ff4602,
    0x2272ff25f5161811,
    0xfffffff3ffffff09,
    0xf2fffff2fffff3f4,
    0xfff3ff54f8f34373,
    0xfffffff6ffffff25,
    0xf8fffff5f71518f7,
    0xfffff727f2f5fff6,
    0xf1ff78272565ff02,
    0xf2ff33f8ff07f205,
    0x0556070427f63374,
    0xfffff2f7fff8ff28,
    0xf6f88076fffff2f6,
    0xfff4ff28f5f48295,
    0xf15661f6fffaf152,
    0xf5f82345f6ff1124,
    0x3a11ff52f0f34373,
    0xff52f73826339645,
    0x72f55607f3034531,
    0x6083485267050700,
  ]

private def ntLabel5 (s : List ℕ) : ℕ := (ntL5 >>> (4 * ntLehmer s)) % 16
private def ntDistance5 (s : List ℕ) : ℕ := (ntD5 >>> (4 * ntLehmer s)) % 16
private def ntLabel6 (s : List ℕ) : ℕ := (ntL6 >>> (5 * ntLehmer s)) % 32
private def ntDistance6 (s : List ℕ) : ℕ := (ntD6 >>> (4 * ntLehmer s)) % 16

private def ntClassOk (n m : ℕ) (reps : List (List ℕ))
    (label distance : List ℕ → ℕ) (s : List ℕ) : Bool :=
  let l := label s
  let d := distance s
  (!ntHasPatB (ntQuads n) s || l < m) &&
    (ntNbrs (ntQuads n) s).all (fun t => label t == l) &&
    (l ≥ m || d < 15 && if d = 0 then s == reps.getD l []
      else (ntNbrs (ntQuads n) s).any fun t => distance t + 1 == d)

-- These finite certificates are evaluated by the kernel.
set_option maxRecDepth 100000 in

private lemma ntRepCode5_mem (k : Fin 9) :
    ntRepCodes5.getD k.val [] ∈ List.permutations' (List.range 5) := by
  fin_cases k <;> decide

set_option maxRecDepth 100000 in
-- Deciding membership among the 720 codes of `S₆` needs extra recursion depth.
private lemma ntRepCode6_mem (k : Fin 26) :
    ntRepCodes6.getD k.val [] ∈ List.permutations' (List.range 6) := by
  fin_cases k <;> decide

private noncomputable def ntRep5 (k : Fin 9) : Equiv.Perm (Fin 5) :=
  ntPermOfCode (ntRepCodes5.getD k.val []) (ntRepCode5_mem k)

private noncomputable def ntRep6 (k : Fin 26) : Equiv.Perm (Fin 6) :=
  ntPermOfCode (ntRepCodes6.getD k.val []) (ntRepCode6_mem k)

private lemma ntCode_rep5 (k : Fin 9) :
    ntCode (ntRep5 k) = ntRepCodes5.getD k.val [] :=
  ntCode_permOfCode _ _

private lemma ntCode_rep6 (k : Fin 26) :
    ntCode (ntRep6 k) = ntRepCodes6.getD k.val [] :=
  ntCode_permOfCode _ _

private lemma ntLabel_rep5 (k : Fin 9) :
    ntLabel5 (ntCode (ntRep5 k)) = k.val := by
  rw [ntCode_rep5]
  fin_cases k <;> decide

set_option maxRecDepth 100000 in
-- Evaluating the `S₆` label table needs extra recursion depth.
private lemma ntLabel_rep6 (k : Fin 26) :
    ntLabel6 (ntCode (ntRep6 k)) = k.val := by
  rw [ntCode_rep6]
  fin_cases k <;> decide

private lemma ntRep5_pat (k : Fin 9) : ntPat 5 (ntRep5 k) := by
  apply ntHasPatB_sound
  rw [ntCode_rep5]
  fin_cases k <;> decide

set_option maxRecDepth 100000 in
-- Evaluating the pattern test on the 26 `S₆` representatives needs extra recursion depth.
private lemma ntRep6_pat (k : Fin 26) : ntPat 6 (ntRep6 k) := by
  apply ntHasPatB_sound
  rw [ntCode_rep6]
  fin_cases k <;> decide

private def ntCert7Block : ℕ → ℕ → Array ℕ
  | 0, 0 => #[
      0, 0, 6, 213, 245, 326, 85, 101, 21, 340, 356, 340, 37, 372,
      4, 4, 545, 67, 388, 372, 4, 4, 147, 15, 20, 212, 37, 213,
      293, 38, 6, 118, 4, 5, 4, 340, 195, 179, 20, 20, 69, 37,
      4, 117, 20, 117, 5, 5, 38, 38, 291, 100, 291, 37, 37, 37,
      101, 36, 70, 83, 481, 497, 6, 36
    ]
  | 0, 1 => #[
      5, 5, 481, 497, 149, 36, 5, 5, 68, 36, 52, 68, 21, 21,
      53, 38, 69, 69, 529, 19, 118, 37, 15, 117, 21, 21, 117, 5,
      5, 6, 513, 3, 69, 420, 68, 117, 69, 69, 132, 83, 69, 86,
      147, 69, 132, 116, 101, 85, 70, 71, 117, 133, 149, 119, 147, 15,
      70, 422, 68, 420, 452, 15, 469, 102
    ]
  | 0, 2 => #[
      436, 420, 69, 69, 468, 85, 101, 85, 69, 69, 532, 229, 133, 117,
      245, 15, 245, 38, 387, 371, 20, 54, 4, 340, 5, 261, 53, 341,
      36, 52, 21, 84, 21, 21, 36, 38, 133, 117, 53, 22, 548, 277,
      19, 19, 19, 19, 53, 54, 52, 21, 99, 21, 5, 37, 52, 6,
      19, 19, 5, 7, 52, 6, 19, 19
    ]
  | 0, 3 => #[
      468, 37, 51, 35, 149, 21, 51, 35, 277, 261, 101, 83, 53, 37,
      133, 15, 21, 23, 147, 5, 4, 117, 5, 4, 468, 261, 131, 115,
      149, 15, 85, 85, 277, 69, 67, 85, 150, 86, 101, 85, 549, 70,
      147, 15, 135, 119, 15, 15, 293, 118, 515, 164, 515, 166, 452, 85,
      500, 484, 245, 85, 211, 227, 227, 211
    ]
  | 0, 4 => #[
      69, 165, 211, 227, 227, 211, 245, 15, 214, 15, 133, 117, 293, 15,
      148, 86, 69, 69, 70, 86, 99, 83, 227, 211, 165, 165, 309, 15,
      227, 211, 15, 15, 321, 321, 53, 37, 53, 37, 37, 37, 132, 116,
      53, 37, 53, 37, 51, 35, 322, 165, 309, 5, 51, 35, 466, 7,
      53, 261, 337, 353, 21, 22, 53, 37
    ]
  | 0, 5 => #[
      275, 259, 20, 22, 53, 37, 53, 39, 405, 15, 3, 3, 517, 5,
      405, 7, 277, 261, 337, 353, 294, 359, 293, 15, 275, 259, 15, 15,
      102, 437, 102, 86, 69, 69, 307, 390, 15, 15, 405, 15, 164, 500,
      164, 164, 164, 166, 149, 182, 243, 165, 195, 181, 101, 85, 101, 86,
      163, 163, 229, 215, 229, 214, 245, 15
    ]
  | 0, 6 => #[
      148, 214, 291, 117, 291, 15, 181, 181, 197, 181, 197, 179, 417, 433,
      102, 86, 69, 69, 417, 433, 230, 213, 469, 15, 261, 277, 133, 117,
      293, 15, 15, 15, 134, 118, 15, 15, 195, 179, 101, 85, 468, 68,
      309, 437, 15, 15, 469, 15, 277, 37, 53, 38, 19, 19, 291, 37,
      52, 261, 21, 20, 369, 385, 54, 37
    ]
  | 0, 7 => #[
      22, 23, 452, 5, 5, 374, 405, 15, 277, 277, 293, 325, 291, 342,
      291, 357, 326, 326, 358, 342, 369, 385, 15, 15, 469, 15, 309, 373,
      404, 373, 406, 15, 165, 181, 165, 213, 165, 165, 228, 179, 277, 261,
      165, 179, 228, 212, 197, 181, 244, 167, 227, 211, 245, 421, 245, 15,
      229, 262, 227, 211, 245, 15, 197, 181
    ]
  | 1, 0 => #[
      276, 260, 465, 166, 246, 182, 197, 181, 166, 166, 309, 421, 230, 422,
      449, 15, 292, 261, 227, 211, 292, 15, 294, 15, 229, 213, 469, 15,
      308, 502, 198, 182, 165, 165, 309, 422, 438, 422, 532, 15, 275, 259,
      293, 262, 469, 15, 309, 15, 278, 263, 534, 15, 310, 15, 15, 15,
      548, 15, 309, 436, 437, 485, 518, 15
    ]
  | 1, 1 => #[
      322, 338, 341, 261, 341, 341, 388, 357, 277, 373, 324, 324, 310, 373,
      356, 340, 401, 326, 373, 374, 390, 374, 406, 15, 309, 485, 244, 213,
      197, 182, 181, 229, 277, 165, 163, 165, 214, 230, 15, 213, 165, 167,
      227, 211, 231, 214, 244, 15, 261, 230, 227, 211, 245, 15, 197, 179,
      276, 260, 198, 165, 246, 181, 229, 15
    ]
  | 1, 2 => #[
      550, 167, 309, 15, 230, 215, 15, 15, 292, 261, 227, 211, 294, 15,
      246, 15, 229, 213, 15, 15, 197, 502, 199, 183, 549, 15, 308, 502,
      15, 15, 532, 15, 275, 259, 279, 262, 293, 15, 309, 15, 278, 263,
      534, 15, 309, 15, 15, 15, 548, 15, 486, 501, 501, 485, 518, 15,
      309, 263, 15, 261, 295, 15, 308, 15
    ]
  | 1, 3 => #[
      277, 15, 15, 15, 311, 15, 15, 15, 550, 15, 15, 15, 15, 15,
      15, 15, 164, 166, 166, 198, 166, 166, 180, 180, 166, 166, 405, 166,
      214, 181, 15, 213, 165, 165, 214, 214, 389, 213, 405, 15, 293, 214,
      246, 214, 246, 15, 182, 182, 164, 164, 164, 164, 197, 181, 229, 15,
      165, 167, 246, 15, 229, 373, 15, 15
    ]
  | 1, 4 => #[
      262, 262, 453, 422, 293, 15, 245, 15, 438, 262, 15, 15, 197, 181,
      197, 183, 167, 15, 469, 501, 15, 15, 519, 15, 420, 436, 437, 261,
      453, 15, 294, 15, 277, 421, 533, 15, 469, 15, 15, 15, 533, 15,
      311, 487, 501, 485, 517, 15, 420, 436, 15, 261, 295, 15, 454, 15,
      277, 15, 15, 15, 311, 15, 15, 15
    ]
  | 1, 5 => #[
      549, 15, 15, 15, 15, 15, 15, 15, 133, 86, 131, 115, 68, 102,
      516, 86, 67, 67, 67, 67, 116, 132, 99, 83, 149, 69, 116, 118,
      150, 119, 149, 15, 245, 118, 20, 117, 22, 15, 149, 358, 4, 15,
      100, 15, 101, 85, 53, 15, 54, 15, 149, 54, 53, 15, 22, 15,
      148, 54, 21, 22, 147, 21, 293, 86
    ]
  | 1, 6 => #[
      21, 15, 101, 15, 53, 37, 54, 15, 67, 15, 53, 37, 54, 15,
      516, 15, 117, 115, 53, 37, 21, 21, 293, 37, 101, 15, 21, 15,
      99, 83, 54, 15, 533, 15, 484, 484, 131, 15, 6, 15, 117, 117,
      150, 118, 149, 15, 101, 102, 100, 15, 69, 15, 99, 83, 102, 15,
      70, 15, 151, 15, 131, 15, 15, 15
    ]
  | 1, 7 => #[
      117, 117, 133, 117, 149, 15, 83, 83, 101, 85, 101, 85, 147, 87,
      99, 83, 69, 70, 147, 15, 135, 119, 15, 15, 244, 118, 131, 115,
      150, 15, 150, 15, 132, 15, 103, 15, 243, 85, 133, 15, 163, 15,
      243, 15, 134, 15, 15, 15, 147, 37, 229, 213, 23, 37, 148, 38,
      53, 15, 53, 15, 53, 37, 99, 15
    ]
  | 2, 0 => #[
      532, 15, 53, 37, 53, 15, 532, 15, 53, 37, 53, 37, 21, 22,
      291, 38, 54, 15, 21, 15, 99, 83, 54, 15, 532, 15, 5, 437,
      516, 15, 6, 15, 309, 327, 134, 357, 343, 359, 291, 15, 277, 15,
      15, 15, 99, 83, 102, 15, 70, 15, 421, 437, 15, 15, 15, 15,
      148, 260, 133, 259, 293, 15, 150, 15
    ]
  | 2, 1 => #[
      131, 115, 15, 15, 309, 85, 101, 86, 67, 67, 309, 438, 15, 15,
      452, 15, 213, 213, 131, 115, 245, 15, 517, 182, 197, 15, 197, 15,
      101, 85, 227, 15, 550, 15, 246, 437, 227, 15, 455, 15, 149, 15,
      227, 211, 15, 15, 150, 15, 15, 15, 15, 15, 101, 85, 103, 15,
      165, 15, 485, 501, 15, 15, 518, 15
    ]
  | 2, 2 => #[
      53, 37, 53, 325, 21, 21, 54, 37, 275, 15, 357, 15, 53, 38,
      53, 15, 22, 15, 484, 484, 6, 15, 453, 15, 309, 390, 325, 325,
      357, 341, 295, 358, 275, 15, 357, 15, 375, 389, 15, 15, 550, 15,
      374, 15, 437, 15, 453, 15, 292, 500, 294, 486, 293, 15, 291, 15,
      502, 263, 470, 15, 309, 15, 15, 15
    ]
  | 2, 3 => #[
      469, 15, 420, 420, 453, 422, 454, 15, 229, 213, 246, 214, 243, 15,
      292, 183, 196, 15, 165, 15, 195, 179, 198, 15, 469, 15, 246, 423,
      437, 15, 453, 15, 246, 15, 230, 215, 470, 15, 245, 15, 278, 15,
      470, 15, 195, 179, 198, 15, 166, 15, 437, 421, 437, 15, 533, 15,
      307, 15, 15, 15, 469, 15, 294, 15
    ]
  | 2, 4 => #[
      279, 15, 533, 15, 15, 15, 15, 15, 532, 15, 517, 438, 516, 15,
      517, 15, 404, 389, 405, 374, 342, 15, 293, 342, 278, 15, 324, 15,
      358, 342, 356, 15, 325, 15, 389, 373, 389, 15, 405, 15, 292, 500,
      277, 261, 293, 15, 291, 15, 277, 261, 15, 15, 309, 15, 15, 15,
      549, 15, 309, 15, 15, 15, 15, 15
    ]
  | 2, 5 => #[
      229, 211, 246, 213, 246, 15, 292, 198, 197, 15, 197, 15, 195, 179,
      198, 15, 166, 15, 246, 15, 231, 15, 15, 15, 310, 15, 229, 215,
      15, 15, 245, 15, 230, 15, 15, 15, 195, 179, 198, 15, 166, 15,
      485, 501, 15, 15, 518, 15, 549, 15, 15, 15, 534, 15, 294, 15,
      279, 15, 533, 15, 15, 15, 15, 15
    ]
  | 2, 6 => #[
      532, 15, 517, 486, 516, 15, 517, 15, 310, 15, 15, 15, 15, 15,
      293, 15, 278, 15, 15, 15, 15, 15, 15, 15, 551, 15, 15, 15,
      15, 15, 15, 15, 389, 262, 403, 260, 403, 326, 308, 342, 276, 324,
      324, 326, 371, 387, 403, 342, 325, 325, 371, 387, 403, 375, 405, 15,
      421, 437, 229, 213, 453, 15, 340, 340
    ]
  | 2, 7 => #[
      164, 164, 164, 164, 245, 341, 198, 341, 325, 325, 403, 15, 230, 373,
      15, 15, 419, 419, 435, 419, 455, 15, 470, 15, 435, 419, 15, 15,
      357, 341, 357, 341, 516, 325, 469, 502, 15, 15, 516, 15, 437, 421,
      451, 423, 453, 15, 451, 15, 278, 421, 534, 15, 469, 15, 15, 15,
      533, 15, 467, 500, 501, 485, 518, 15
    ]
  | 3, 0 => #[
      437, 421, 451, 423, 454, 15, 467, 15, 279, 421, 15, 15, 470, 15,
      15, 15, 550, 15, 467, 15, 15, 15, 15, 15, 262, 262, 15, 421,
      453, 15, 454, 15, 437, 15, 15, 15, 469, 15, 15, 15, 551, 15,
      15, 15, 15, 15, 15, 15, 372, 372, 227, 211, 246, 15, 180, 180,
      325, 15, 166, 15, 357, 181, 229, 15
    ]
  | 3, 1 => #[
      325, 15, 246, 15, 387, 15, 15, 15, 405, 15, 227, 211, 15, 15,
      451, 15, 231, 15, 15, 15, 197, 341, 357, 15, 166, 15, 487, 503,
      15, 15, 15, 15, 310, 15, 15, 15, 533, 15, 294, 15, 435, 15,
      535, 15, 15, 15, 15, 15, 535, 15, 517, 15, 502, 15, 519, 15,
      309, 15, 15, 15, 15, 15, 294, 15
    ]
  | 3, 2 => #[
      277, 15, 15, 15, 15, 15, 15, 15, 550, 15, 15, 15, 15, 15,
      15, 15, 1, 1, 133, 485, 149, 7, 85, 85, 101, 53, 37, 53,
      101, 21, 131, 115, 34, 52, 21, 21, 131, 115, 36, 15, 117, 117,
      133, 117, 151, 15, 149, 86, 101, 15, 101, 15, 101, 86, 133, 15,
      69, 15, 149, 15, 133, 15, 15, 15
    ]
  | 3, 3 => #[
      245, 38, 131, 115, 84, 38, 149, 15, 131, 15, 55, 15, 2, 2,
      53, 15, 6, 15, 2, 2, 54, 15, 452, 15, 51, 35, 53, 37,
      22, 196, 147, 37, 134, 15, 530, 15, 101, 85, 52, 15, 548, 15,
      212, 228, 502, 15, 2, 15, 164, 69, 85, 102, 181, 196, 147, 15,
      134, 15, 15, 15, 101, 85, 103, 15
    ]
  | 3, 4 => #[
      69, 15, 212, 228, 15, 15, 290, 15, 149, 501, 501, 5, 5, 5,
      17, 17, 134, 117, 38, 55, 21, 21, 100, 53, 36, 50, 21, 21,
      37, 53, 15, 52, 149, 15, 133, 117, 15, 15, 149, 15, 499, 15,
      15, 15, 102, 85, 101, 15, 452, 15, 423, 438, 15, 15, 452, 15,
      243, 69, 133, 117, 181, 103, 149, 15
    ]
  | 3, 5 => #[
      135, 15, 15, 15, 116, 132, 15, 15, 164, 15, 117, 134, 15, 15,
      468, 15, 51, 35, 85, 101, 21, 21, 53, 37, 52, 15, 406, 15,
      54, 38, 55, 15, 18, 15, 6, 388, 514, 15, 404, 15, 547, 357,
      181, 101, 404, 197, 341, 357, 327, 15, 358, 15, 117, 132, 15, 15,
      306, 15, 118, 388, 452, 15, 404, 15
    ]
  | 3, 6 => #[
      309, 5, 499, 483, 2, 4, 534, 22, 33, 49, 39, 54, 532, 21,
      38, 54, 37, 53, 20, 15, 37, 53, 37, 53, 550, 15, 15, 15,
      470, 15, 515, 15, 277, 15, 470, 15, 15, 15, 15, 15, 469, 15,
      421, 436, 453, 15, 454, 15, 548, 70, 85, 101, 469, 102, 243, 15,
      230, 15, 470, 15, 197, 181, 199, 15
    ]
  | 3, 7 => #[
      515, 15, 212, 228, 453, 15, 292, 15, 68, 69, 182, 198, 86, 100,
      15, 15, 15, 15, 468, 15, 260, 228, 15, 15, 549, 15, 114, 130,
      502, 15, 452, 15, 372, 372, 340, 356, 325, 356, 388, 372, 388, 15,
      358, 15, 259, 275, 358, 15, 549, 15, 259, 275, 405, 15, 405, 15,
      5, 5, 499, 483, 4, 15, 293, 23
    ]
  | 4, 0 => #[
      33, 49, 38, 55, 21, 21, 38, 54, 37, 54, 18, 20, 37, 54,
      37, 53, 310, 15, 15, 15, 15, 15, 515, 15, 277, 15, 15, 15,
      15, 15, 15, 15, 551, 15, 15, 15, 15, 15, 15, 15, 245, 166,
      85, 101, 86, 102, 243, 15, 230, 15, 15, 15, 197, 181, 198, 15,
      149, 15, 116, 132, 15, 15, 531, 15
    ]
  | 4, 1 => #[
      68, 70, 182, 198, 85, 100, 15, 15, 15, 15, 534, 15, 260, 276,
      15, 15, 244, 15, 114, 130, 502, 15, 518, 15, 70, 70, 85, 101,
      85, 101, 15, 15, 15, 15, 15, 15, 214, 134, 15, 15, 150, 15,
      118, 278, 15, 15, 15, 15, 453, 374, 340, 326, 405, 15, 292, 342,
      325, 325, 355, 341, 373, 339, 405, 342
    ]
  | 4, 2 => #[
      325, 325, 374, 389, 389, 374, 405, 15, 308, 374, 451, 422, 451, 15,
      341, 341, 357, 341, 357, 339, 403, 341, 358, 342, 323, 326, 403, 15,
      390, 373, 15, 15, 451, 437, 229, 373, 453, 199, 469, 15, 390, 374,
      15, 15, 357, 341, 355, 181, 548, 326, 469, 502, 15, 15, 517, 15,
      469, 167, 181, 422, 453, 199, 451, 15
    ]
  | 4, 3 => #[
      438, 421, 534, 15, 213, 229, 15, 15, 533, 15, 261, 277, 517, 486,
      246, 15, 469, 421, 453, 197, 454, 199, 451, 15, 439, 423, 15, 15,
      213, 229, 15, 15, 550, 15, 261, 277, 15, 15, 15, 15, 420, 420,
      515, 422, 515, 15, 469, 15, 438, 421, 15, 15, 531, 15, 15, 15,
      549, 15, 531, 15, 15, 15, 15, 15
    ]
  | 4, 4 => #[
      373, 373, 389, 373, 405, 15, 405, 342, 357, 15, 357, 15, 357, 343,
      387, 15, 325, 15, 406, 15, 387, 15, 15, 15, 161, 161, 389, 373,
      182, 199, 245, 15, 230, 15, 15, 15, 197, 229, 357, 15, 162, 15,
      213, 229, 15, 15, 306, 15, 469, 166, 177, 193, 534, 198, 454, 15,
      435, 15, 533, 15, 261, 277, 15, 15
    ]
  | 4, 5 => #[
      245, 15, 213, 500, 502, 15, 245, 15, 469, 167, 177, 193, 182, 199,
      455, 15, 435, 15, 15, 15, 214, 277, 15, 15, 309, 15, 213, 230,
      15, 15, 245, 15, 485, 501, 517, 487, 517, 15, 293, 15, 278, 422,
      15, 15, 533, 15, 15, 15, 550, 15, 533, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 294, 15
    ]
  | 4, 6 => #[
      438, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 405, 167, 387, 197, 181, 15, 245, 15, 389, 15, 15, 15,
      420, 388, 199, 15, 292, 15, 213, 436, 15, 15, 292, 15, 165, 165,
      342, 199, 15, 197, 15, 15, 15, 15, 534, 15, 261, 278, 15, 15,
      404, 15, 214, 229, 518, 15, 292, 15
    ]
  | 4, 7 => #[
      165, 15, 183, 358, 181, 197, 15, 15, 15, 15, 15, 15, 261, 389,
      15, 15, 245, 15, 372, 229, 15, 15, 292, 15, 533, 486, 515, 52,
      515, 5, 515, 5, 132, 485, 6, 6, 99, 83, 36, 52, 452, 38,
      531, 277, 37, 22, 452, 54, 149, 23, 37, 101, 85, 15, 6, 7,
      499, 15, 5, 15, 101, 277, 101, 15
    ]
  | 5, 0 => #[
      293, 15, 117, 277, 22, 15, 293, 15, 65, 65, 134, 102, 86, 103,
      149, 15, 132, 15, 15, 15, 261, 133, 103, 15, 66, 15, 117, 133,
      15, 15, 306, 15, 84, 100, 53, 37, 84, 98, 53, 37, 70, 15,
      244, 15, 117, 133, 15, 15, 308, 15, 5, 500, 242, 15, 150, 15,
      164, 102, 85, 100, 100, 100, 117, 229
    ]
  | 5, 1 => #[
      69, 15, 244, 15, 213, 133, 15, 15, 308, 15, 246, 134, 242, 15,
      150, 15, 515, 4, 5, 5, 6, 53, 5, 5, 37, 5, 469, 6,
      21, 53, 22, 22, 148, 53, 261, 436, 22, 53, 309, 53, 531, 69,
      38, 55, 15, 101, 6, 6, 6, 15, 470, 15, 38, 278, 21, 15,
      548, 15, 118, 133, 453, 15, 308, 15
    ]
  | 5, 2 => #[
      550, 70, 81, 97, 470, 102, 15, 15, 15, 15, 469, 15, 484, 501,
      15, 15, 149, 15, 117, 436, 438, 15, 292, 15, 117, 69, 69, 196,
      194, 86, 117, 134, 165, 15, 148, 15, 214, 230, 15, 15, 148, 15,
      117, 134, 150, 15, 146, 15, 68, 164, 162, 101, 197, 181, 118, 388,
      404, 15, 307, 15, 117, 341, 406, 15
    ]
  | 5, 3 => #[
      149, 15, 148, 118, 293, 15, 291, 15, 515, 6, 5, 6, 36, 52,
      5, 7, 37, 53, 6, 54, 21, 21, 22, 22, 148, 53, 37, 53,
      36, 52, 148, 37, 69, 15, 39, 54, 85, 53, 6, 7, 6, 15,
      7, 15, 262, 54, 21, 15, 53, 15, 38, 133, 23, 15, 308, 15,
      70, 71, 81, 97, 86, 103, 15, 15
    ]
  | 5, 4 => #[
      15, 15, 15, 15, 484, 134, 15, 15, 517, 15, 117, 500, 15, 15,
      292, 15, 549, 68, 68, 165, 85, 196, 181, 133, 70, 15, 148, 15,
      214, 230, 15, 15, 148, 15, 117, 486, 150, 15, 146, 15, 66, 68,
      70, 68, 197, 181, 86, 133, 70, 15, 148, 15, 117, 133, 15, 15,
      547, 15, 148, 15, 293, 15, 294, 15
    ]
  | 5, 5 => #[
      405, 486, 389, 373, 405, 326, 453, 358, 437, 341, 405, 326, 389, 373,
      387, 371, 292, 327, 389, 373, 387, 371, 292, 15, 374, 15, 387, 371,
      453, 15, 517, 342, 436, 420, 327, 326, 261, 342, 387, 371, 326, 326,
      469, 277, 387, 371, 295, 15, 452, 438, 387, 371, 454, 15, 454, 15,
      389, 373, 15, 15, 262, 279, 358, 342
    ]
  | 5, 6 => #[
      325, 325, 469, 278, 15, 15, 518, 15, 437, 421, 435, 419, 197, 181,
      181, 197, 435, 419, 197, 181, 213, 231, 15, 15, 534, 15, 244, 214,
      501, 485, 293, 15, 437, 421, 435, 419, 197, 181, 181, 197, 435, 419,
      197, 181, 470, 229, 15, 15, 550, 15, 292, 15, 246, 214, 293, 15,
      452, 500, 453, 486, 453, 15, 451, 15
    ]
  | 5, 7 => #[
      502, 486, 15, 15, 469, 279, 15, 15, 549, 15, 469, 279, 15, 15,
      15, 15, 405, 374, 405, 374, 407, 15, 452, 15, 357, 15, 359, 15,
      257, 273, 389, 15, 294, 15, 257, 273, 391, 15, 309, 15, 549, 15,
      390, 375, 15, 15, 405, 15, 438, 15, 15, 15, 355, 339, 358, 15,
      308, 15, 261, 277, 15, 15, 309, 15
    ]
  | 6, 0 => #[
      213, 165, 165, 166, 181, 181, 451, 197, 166, 15, 309, 15, 209, 225,
      15, 15, 532, 15, 213, 229, 228, 15, 245, 15, 165, 165, 165, 165,
      244, 182, 451, 197, 437, 15, 198, 15, 209, 225, 15, 15, 309, 15,
      213, 213, 244, 15, 246, 15, 469, 502, 501, 485, 518, 15, 517, 15,
      435, 419, 15, 15, 262, 279, 15, 15
    ]
  | 6, 1 => #[
      293, 15, 533, 278, 15, 15, 292, 15, 550, 15, 15, 15, 15, 15,
      453, 15, 437, 15, 15, 15, 263, 279, 15, 15, 293, 15, 263, 279,
      15, 15, 293, 15, 326, 327, 342, 358, 342, 359, 403, 15, 390, 15,
      15, 15, 357, 341, 359, 15, 293, 15, 374, 437, 15, 15, 292, 15,
      165, 165, 166, 166, 182, 182, 182, 199
    ]
  | 6, 2 => #[
      165, 15, 197, 15, 374, 438, 15, 15, 308, 15, 260, 276, 292, 15,
      404, 15, 181, 197, 166, 166, 181, 197, 183, 198, 165, 15, 244, 15,
      422, 390, 15, 15, 245, 15, 260, 276, 245, 15, 404, 15, 517, 15,
      499, 483, 517, 15, 533, 15, 499, 483, 15, 15, 421, 437, 15, 15,
      308, 15, 421, 437, 15, 15, 308, 15
    ]
  | 6, 3 => #[
      549, 15, 15, 15, 15, 15, 515, 15, 503, 15, 15, 15, 262, 279,
      15, 15, 292, 15, 263, 278, 15, 15, 292, 15, 549, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15, 486, 15, 15, 15, 308, 15,
      15, 502, 15, 15, 452, 15, 165, 165, 181, 325, 182, 198, 341, 15,
      165, 15, 246, 15, 214, 231, 15, 15
    ]
  | 6, 4 => #[
      244, 15, 258, 274, 246, 15, 244, 15, 549, 197, 182, 197, 244, 197,
      15, 357, 168, 15, 404, 15, 215, 230, 15, 15, 244, 15, 258, 274,
      244, 15, 244, 15, 2, 2, 37, 5, 36, 52, 20, 21, 5, 21,
      4, 4, 6, 21, 4, 4, 3, 6, 22, 22, 34, 50, 19, 54,
      36, 69, 37, 69, 38, 52, 37, 6
    ]
  | 6, 5 => #[
      22, 15, 4, 15, 6, 6, 4, 15, 5, 15, 132, 116, 148, 15,
      21, 15, 85, 69, 20, 20, 53, 101, 38, 15, 20, 15, 150, 15,
      113, 129, 6, 15, 517, 15, 51, 35, 277, 15, 21, 15, 69, 101,
      70, 70, 85, 101, 86, 103, 69, 15, 531, 15, 117, 133, 15, 15,
      533, 15, 260, 276, 149, 15, 515, 15
    ]
  | 6, 6 => #[
      149, 86, 85, 101, 340, 340, 130, 114, 245, 15, 149, 15, 132, 116,
      134, 15, 164, 15, 229, 213, 133, 15, 149, 15, 2, 2, 501, 5,
      36, 52, 20, 22, 5, 485, 4, 4, 6, 20, 4, 4, 3, 38,
      116, 116, 34, 50, 19, 22, 20, 52, 70, 53, 85, 85, 517, 53,
      22, 15, 148, 15, 6, 6, 6, 15
    ]
  | 6, 7 => #[
      5, 15, 132, 116, 20, 15, 21, 15, 69, 69, 21, 102, 52, 36,
      15, 54, 24, 15, 52, 15, 113, 129, 7, 15, 5, 15, 51, 35,
      148, 15, 533, 15, 69, 69, 70, 70, 149, 101, 87, 102, 69, 15,
      531, 15, 117, 133, 15, 15, 533, 15, 260, 276, 149, 15, 515, 15,
      148, 70, 70, 118, 70, 15, 130, 114
    ]
  | 7, 0 => #[
      245, 15, 69, 15, 132, 116, 101, 15, 69, 15, 229, 213, 148, 15,
      150, 15, 324, 372, 357, 341, 310, 326, 357, 341, 357, 340, 325, 325,
      390, 374, 358, 342, 323, 323, 403, 276, 293, 262, 294, 15, 452, 375,
      389, 422, 403, 15, 357, 341, 356, 341, 309, 325, 355, 339, 358, 342,
      309, 327, 294, 263, 293, 262, 293, 15
    ]
  | 7, 1 => #[
      437, 421, 438, 373, 453, 15, 15, 15, 390, 374, 310, 15, 355, 339,
      359, 343, 326, 326, 277, 261, 277, 261, 532, 15, 451, 421, 438, 422,
      308, 15, 455, 15, 438, 422, 533, 15, 469, 15, 15, 15, 548, 15,
      470, 485, 276, 260, 517, 15, 228, 212, 244, 214, 182, 15, 453, 182,
      166, 166, 165, 166, 198, 182, 196, 212
    ]
  | 7, 2 => #[
      165, 167, 229, 213, 229, 213, 245, 15, 421, 486, 437, 419, 309, 15,
      455, 15, 435, 421, 311, 15, 469, 15, 15, 15, 550, 15, 262, 15,
      279, 262, 295, 15, 389, 373, 387, 371, 405, 15, 357, 343, 358, 15,
      305, 15, 357, 343, 357, 15, 310, 15, 262, 261, 278, 15, 289, 15,
      550, 15, 387, 371, 309, 15, 406, 15
    ]
  | 7, 3 => #[
      15, 15, 309, 15, 486, 341, 359, 15, 325, 15, 277, 262, 278, 15,
      293, 15, 469, 15, 15, 15, 310, 15, 454, 15, 439, 15, 534, 15,
      15, 15, 15, 15, 310, 15, 292, 276, 294, 15, 518, 15, 162, 178,
      181, 181, 181, 181, 228, 213, 437, 15, 245, 15, 244, 213, 198, 15,
      241, 15, 213, 214, 230, 15, 246, 15
    ]
  | 7, 4 => #[
      501, 485, 501, 485, 517, 15, 451, 15, 501, 485, 310, 15, 533, 15,
      15, 15, 309, 15, 260, 260, 293, 263, 294, 15, 534, 15, 15, 15,
      15, 15, 453, 15, 437, 15, 311, 15, 15, 15, 15, 15, 310, 15,
      261, 261, 294, 15, 295, 15, 403, 325, 342, 358, 310, 359, 407, 15,
      391, 15, 310, 15, 358, 342, 15, 15
    ]
  | 7, 5 => #[
      324, 15, 260, 276, 277, 15, 533, 15, 549, 326, 341, 357, 309, 359,
      15, 15, 15, 15, 309, 15, 420, 390, 15, 15, 532, 15, 260, 276,
      516, 15, 293, 15, 181, 197, 228, 197, 164, 164, 212, 212, 245, 15,
      164, 15, 197, 181, 230, 15, 165, 15, 213, 229, 229, 15, 453, 15,
      515, 487, 502, 486, 306, 15, 519, 15
    ]
  | 7, 6 => #[
      502, 486, 310, 15, 532, 439, 15, 15, 308, 15, 262, 262, 292, 262,
      294, 15, 533, 15, 15, 15, 310, 15, 518, 15, 503, 15, 310, 15,
      421, 437, 15, 15, 309, 15, 261, 276, 293, 15, 468, 15, 548, 15,
      15, 15, 309, 15, 15, 15, 15, 15, 311, 15, 484, 440, 15, 15,
      515, 15, 262, 500, 277, 15, 454, 15
    ]
  | 7, 7 => #[
      326, 325, 325, 326, 308, 342, 373, 360, 327, 15, 306, 15, 373, 389,
      15, 15, 310, 15, 277, 261, 278, 15, 290, 15, 180, 196, 180, 180,
      163, 180, 182, 196, 242, 15, 165, 15, 195, 179, 198, 15, 549, 15,
      213, 229, 404, 15, 245, 15, 501, 486, 516, 487, 310, 15, 15, 15,
      503, 486, 309, 15, 535, 15, 15, 15
    ]
  | 8, 0 => #[
      550, 15, 290, 260, 438, 262, 293, 15, 535, 15, 15, 15, 310, 15,
      519, 15, 15, 15, 309, 15, 15, 15, 15, 15, 310, 15, 276, 277,
      276, 15, 293, 15, 551, 15, 15, 15, 310, 15, 15, 15, 15, 15,
      309, 15, 486, 503, 15, 15, 310, 15, 437, 276, 278, 15, 531, 15,
      15, 15, 15, 15, 310, 15, 15, 15
    ]
  | 8, 1 => #[
      15, 15, 310, 15, 15, 15, 15, 15, 15, 15, 262, 501, 15, 15,
      294, 15, 178, 194, 166, 166, 165, 165, 182, 228, 246, 15, 196, 15,
      197, 181, 15, 15, 547, 15, 373, 228, 230, 15, 246, 15, 6, 100,
      132, 53, 2, 34, 4, 116, 67, 53, 52, 67, 18, 34, 101, 20,
      69, 38, 116, 132, 148, 118, 149, 15
    ]
  | 8, 2 => #[
      84, 100, 36, 101, 68, 68, 5, 52, 4, 15, 69, 15, 132, 133,
      132, 15, 549, 15, 36, 36, 149, 15, 21, 15, 66, 82, 85, 21,
      100, 84, 132, 52, 19, 15, 102, 15, 5, 5, 134, 15, 145, 15,
      117, 5, 3, 15, 5, 15, 100, 84, 84, 100, 21, 19, 116, 132,
      150, 15, 21, 15, 101, 85, 15, 15
    ]
  | 8, 3 => #[
      21, 15, 500, 5, 3, 15, 7, 15, 70, 70, 82, 98, 67, 70,
      116, 132, 146, 15, 69, 15, 99, 83, 102, 15, 71, 15, 117, 118,
      134, 15, 150, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15
    ]
  | 8, 4 => #[
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15
    ]
  | 8, 5 => #[
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15
    ]
  | 8, 6 => #[
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15
    ]
  | 8, 7 => #[
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15
    ]
  | 9, 0 => #[
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15
    ]
  | 9, 1 => #[
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15
    ]
  | 9, 2 => #[
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15
    ]
  | 9, 3 => #[
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15
    ]
  | 9, 4 => #[
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15
    ]
  | 9, 5 => #[
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15
    ]
  | 9, 6 => #[
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15
    ]
  | _, _ => #[]

private def ntCert7Entry (s : List ℕ) : ℕ :=
  let rank := ntLehmer s
  (ntCert7Block (rank / 512) (rank / 64 % 8)).getD (rank % 64) 15

private def ntDist7 (s : List ℕ) : ℕ :=
  ntCert7Entry s % 16

private def ntDeleteCode (s : List ℕ) (y : ℕ) : List ℕ :=
  let v := s.getD y 0
  (s.eraseIdx y).map fun x => if v < x then x - 1 else x

private def ntInsertCodeZero (v : ℕ) (s : List ℕ) : List ℕ :=
  v :: s.map fun x => if x < v then x else x + 1

private def ntOk7 (s : List ℕ) : Bool :=
  let entry := ntCert7Entry s
  let d := entry % 16
  let q := ntQuads 7
  let i := entry / 16
  (d < 15 || !ntIsGB 7 q s) &&
    (d ≥ 15 || if d = 0 then
      (s == List.range 7 || s == (List.range 5 ++ [6, 5]))
    else i < q.length && match ntNbrAt s (q.getD i (0, 0, 0, 0)) with
      | some t => ntDist7 t + 1 == d
      | none => false)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in

private lemma ntG7_of_eqvGen {σ τ : Equiv.Perm (Fin 7)}
    (hτ : τ ∈ ntG 6) (hστ : Relation.EqvGen (ntMove 7) σ τ) : σ ∈ ntG 6 := by
  refine ⟨?_, ?_, ?_⟩
  · exact (ntClosed_mem (ntE_closed (m := 5)) hστ).2 hτ.1
  · let P : Set (Equiv.Perm (Fin 7)) := {π | ntPat 7 π}
    have hP : ∀ x ∈ P, ∀ y, (ntMove 7 x y ∨ ntMove 7 y x) → y ∈ P := by
      intro x _ y hxy
      exact ntMove_pat (Or.symm hxy)
    exact (ntClosed_mem hP hστ).2 hτ.2.1
  · intro j hj hσK
    by_cases hj0 : j = 0
    · subst j
      rw [ntK_zero_empty hj] at hσK
      exact hσK
    · have hj1 : 1 ≤ j := by omega
      have hK : ∀ x ∈ ntK 7 j hj, ∀ y,
          (ntMove 7 x y ∨ ntMove 7 y x) → y ∈ ntK 7 j hj := by
        intro x hx y hxy
        exact ntK_closed (by omega) hj1 hj hx hxy
      have hτK : τ ∈ ntK 7 j hj :=
        (ntClosed_mem hK hστ).1 hσK
      exact hτ.2.2 j hj hτK

private lemma ntDist7_lt_memG (σ : Equiv.Perm (Fin 7))
    (hσ : ntDist7 (ntCode σ) < 15) : σ ∈ ntG 6 := by
  rcases ntDist7_reaches σ hσ with heven | hodd
  · exact ntG7_of_eqvGen (ntEven_memG (m := 5) (by omega)) heven
  · exact ntG7_of_eqvGen (ntOdd_memG (m := 5) (by omega)) hodd

/-- The `S_5` count. -/
private lemma ntSmall5 : ntncl (ntMove 5) Set.univ = 9 := by
  apply ntNcl_eq_of_reps (x := ntRep5)
  · intro k
    simp
  · intro k
    exact (ntNcl_nontrivial_iff (fun _ _ h => ntMove_ne h)).2
      (ntPat_move (ntRep5_pat k))
  · intro k l hkl hrel
    have hlabel := ntEqvGen_label_eq ntCertificate5 hrel
    rw [ntLabel_rep5, ntLabel_rep5] at hlabel
    exact hkl (Fin.ext hlabel)
  · intro z _ hnontrivial
    obtain ⟨w, hstep⟩ :=
      (ntNcl_nontrivial_iff (fun _ _ h => ntMove_ne h)).1 hnontrivial
    have hpat : ntPat 5 z := ntMove_pat hstep
    have hlt : ntLabel5 (ntCode z) < 9 := ntPat_label_lt ntCertificate5 hpat
    let k : Fin 9 := ⟨ntLabel5 (ntCode z), hlt⟩
    refine ⟨k, ntDistance_reaches ntRep5 ntCode_rep5 ntCertificate5 z k ?_⟩
    rfl

/-- The `S_6` count. -/
private lemma ntSmall6 : ntncl (ntMove 6) Set.univ = 26 := by
  apply ntNcl_eq_of_reps (x := ntRep6)
  · intro k
    simp
  · intro k
    exact (ntNcl_nontrivial_iff (fun _ _ h => ntMove_ne h)).2
      (ntPat_move (ntRep6_pat k))
  · intro k l hkl hrel
    have hlabel := ntEqvGen_label_eq ntCertificate6 hrel
    rw [ntLabel_rep6, ntLabel_rep6] at hlabel
    exact hkl (Fin.ext hlabel)
  · intro z _ hnontrivial
    obtain ⟨w, hstep⟩ :=
      (ntNcl_nontrivial_iff (fun _ _ h => ntMove_ne h)).1 hnontrivial
    have hpat : ntPat 6 z := ntMove_pat hstep
    have hlt : ntLabel6 (ntCode z) < 26 := ntPat_label_lt ntCertificate6 hpat
    let k : Fin 26 := ⟨ntLabel6 (ntCode z), hlt⟩
    refine ⟨k, ntDistance_reaches ntRep6 ntCode_rep6 ntCertificate6 z k ?_⟩
    rfl

/-- Every generic element of `S_7` reaches a reference permutation. -/
private lemma ntSmall7 {σ : Equiv.Perm (Fin 7)} (hσ : σ ∈ ntG 6) :
    Relation.EqvGen (ntMove 7) σ (ntEven 7) ∨
      Relation.EqvGen (ntMove 7) σ (ntOdd 5) := by
  have hok := (List.all_eq_true.mp ntCertificate7) (ntCode σ)
    (ntCode_mem_permutations' σ)
  have hG := ntIsGB_of_memG7 hσ
  dsimp only [ntOk7] at hok
  rw [Bool.and_eq_true] at hok
  have hlt : ntDist7 (ntCode σ) < 15 := by
    have hfirst := hok.1
    change (ntDist7 (ntCode σ) < 15 || !ntIsGB 7 (ntQuads 7) (ntCode σ)) =
      true at hfirst
    rw [hG] at hfirst
    simpa only [Bool.not_true, Bool.or_false, decide_eq_true_eq] using hfirst
  exact ntDist7_reaches σ hlt

private def ntDeletionChoiceBlock : ℕ → Array ℕ
  | 0 => #[
      0x400000000000000000000000,
      0x20000080000000000000000000000000000000030000000000000000000000,
      0x4000000000000000,
      0x320020000000000000200000000000002000000000000000,
      0x22002000000000000020002030000000,
      0x3000000000000000000000003022000000002200200000000000002000000000,
      0x202200000000220022200000200000000000000000200000,
      0x20000030000000000000000000000030000020220000000000000020000000,
      0x2000002028202000202000002000000000002000202000002000000000000000,
      0x2000000000200000400000000200000000000000400000000000000000000000,
      0x2020020020000020232020002020000020220020000022002020000022002000,
      0x1100100010000000001000008000000001000000000000008222222022202220,
      0x1110111010100100100000101310100010100000101100100000110010100000,
      0x10100010100010100010000040000000000000000000000081111110,
      0x3310301010001010003000001010001030001010000000001010001010001010,
      0x1000101000000000221020101000101010200000310010000000000000100000,
      0x1010000031220010100022102000000010100020100010100000000010100010,
      0x2022001010002211202100102010001010001010002000003011000000001100,
      0x1110100010100000301010202200101000000000201000101000101000000000,
      0x2020111020100010100020102020001020100010100010100020000030000010,
      0x8111101012101100101000004010001010001010001000002010002082212010,
      0x3221201020201110202200201000221020210010221020102000101000200000,
      0x10000040000000000000000000000088228220222122202081121020100020,
      0x1000001012101000101000001011000000001100101000001100100000000000,
      0x1000101000100000811111101110111010800100811110101110110010100000,
      0x1081111010101010311110101010111011110010100011101011001011101010,
      0x3310301010001010003000003000000000000000000000008811811011111110,
      0x1000331030000000101000301000101000000000101000101000101010000000,
      0x2000000030110010100011101031001001000000000000000000000030330010,
      0x3010002022001010000000002010001010001010000000002022001011002210,
      0x1000201020000000301000101111101010301110000010000000000000000000,
      0x10000040100010100010100000000020100080220020112100000020100010,
      0x2022002010002210200000008811811021111110108111100000000000000000,
      0x100000828800202200882181000000201000302200201121000000,
      0x1000000010110000000011001000000011001000000000000010000040000000,
      0x8111101011101100102000008111001011001100100000001000001012001000,
      0x2100101010000000101100101000111010000000111010101000101000100000,
      0x1081118181111010111011001010000080110010110011101000000010100010,
      0x1010003011001011110100001011001010001110101000008811811111111110,
      0x1000101000300000000000000000000000000000808800101100881181000010,
      0x50100010110010100000000030330010100033103000000030100010,
      0x3010001010001010000100000000000000000000000000005010003033001010,
      0x1000101000000000801000202200201000000000301000101100301131000000,
      0x8100000040100010200010100000001000000000000000000000000050100010,
      0x8020208088002020000000005010002022002010000000008088002011008811,
      0x110010100000100000000000000000100010400000000000000000000000,
      0x1020000080001010110000000000000010000010120000000000000010110000,
      0x1011001010001110101100101010001010001010101000008111001011001100,
      0x1100110010100000801000101100101000000000101000102100101000000000,
      0x10110010100011101000000080110010110011101081112080110010,
      0x8011001011001100101000108020001011002010000000001010002011001010,
      0x1100101010000000808801101110881188811110801100101100111010811110,
      0x80100080880010100100000050100010,
      0x5010003033003010000000004010001010003010300000004010001010001010,
      0x2000101000000000000000000000000000000000801000101000101000000000,
      0x20000080100080880030100000000040200020100030100100000040100010,
      0x1000000000000000001000004000000000000000000000008020002020002020,
      0x100000100000101310100010100000100000000000100011100000,
      0x1010001010100010100010100010000080001010111010001020000080000000,
      0x8010001010001010000000001010001031111010101011101010001010001011,
      0x1100101010000000801000101111101010811120800000101110100010100000,
      0x1010000080200010100020100000000010100030110010111100000010100010,
      0x8020001011008011828011108010001011001010108011108000001011001000,
      0x1110100011100000801000202000101000000000501000101100101000000000
    ]
  | 1 => #[
      0x8180111180100010110080118180111080100010111110111080111080000010,
      0x4000000000000000000000008010001011001010000000008011008188818011,
      0x3300301000000000403000301000301000000000401000103000101000000000,
      0x1111111141111111111111111111111180300030300030300000000050100030,
      0x1111111118111111111111111111111111111111111111111111111111111111,
      0x1111111111111111811111111111111111211111811111111111111111111111,
      0x1181111111111111811111111111111111111111111111111111111111111111,
      0x8811811111111111118111218111111111111111111111118811811111111111,
      0x1111881181111111111111811111111111111111111111111111111111111111,
      0x8281111181111111111111111181111181111111111111111111111181881111,
      0x8111118188111111111111118111111111111111111111118188111111118811,
      0x1111811181811111811111111111111111811111811111111111111111111111,
      0x1111111181111111111111111111111181111181888181118181111181111111,
      0x8188118111118811818111118811811181111111118111118111111118111111,
      0x888888818881888181811811811111818881811181811111,
      0x40000000,
      0x8000000000000000002000008000000000000000000000000000000008000000,
      0x8000000000000000000000000000000000000000000000000000000000000000,
      0x80002080000000000000000000000088008000000000000080000000000000,
      0x8000000000000000000000000000000000000000008800800000000000,
      0x800000800000000000000000000000808800000000880080000000,
      0x80000000000000000000000080880000000088008280000080000000,
      0x8000000000000000008000008000000000000000000000008000008088000000,
      0x800000808880800080800000800000000000800080800000,
      0x8080000088008000800000000080000080000000080000000000000080000000,
      0x8888888088808880808008008000008088808000808000008088008000008800,
      0x220020200000220020002000000000200000400000000200000000000000,
      0x82222220222022202020020020000020232020002020000020220020,
      0x7070007070007070000000007070007070007070004000008000000000000000,
      0x200000837030707000707000500000707000707000707000000000,
      0x70700070700070700000000072702070700070702040000032002000,
      0x3022000000002200202000007372007070007270200000007070007070007070,
      0x7000707000000000707200707000727220220020707000707000707000300000,
      0x30000030000020222020002020000070703070720070700000000070700070,
      0x7070007082227070202022207070007070007070202000207070007070007070,
      0x7000707000400000822220202220220020200000707000707000707000400000,
      0x2082222070700070722270702020222070720070700072702022002072702070,
      0x2200200000000000002000008000000000000000000000008872827072227270,
      0x2220220020800000200000203220200020200000202200000000220020200000,
      0x1011001081701070700070700080000081111110111011101010010088228020,
      0x8871817071117170108111107070107071117070101011107171007070007170,
      0x7000707010000000737030707000707000400000300000000000000000000000,
      0x70730070700073703000000070700070700070700000000070700070,
      0x7072007071007270200000007071007070007170103100100100000000000000,
      0x707000707200707000000000707000707000707000000000,
      0x2100000070700070700070702000000070700070711170701030111000001000,
      0x5000007070007070007070000000007070008072007071,
      0x7200707121000000707200707000727020000000887181707111717010811110,
      0x80000080000000000000000010000088880070720088718100000070700070,
      0x2000003022002000200000002022000000002200200000008800800000000000,
      0x7000707000400000811110101110110010100000828800202200880080000000,
      0x1000000070700070710070701000000070710070700071701000000071701070,
      0x8871817171118170808111118811801011101100108000008071007071007170,
      0x7100887181000010707000707100707111010000707100707000717010100000,
      0x3000000070700070700070700030000000000000000000000000000080880070,
      0x7070007073007070000000007070007071007070000000007073007070007370,
      0x7100707131000000707000707000707000010000000000000000000000000000,
      0x70700070700070700000000080700070720070700000000070700070,
      0x8088007071008871810000007070007070007070000000100000000000000000,
      0x807080808800707000000000707000707200707000000000,
      0x80880000000088008080000080000000000000000080001080000000,
      0x8111001011001100101000008000208088000000000000005000002022000000,
      0x7100707000000000707100707000717010110010707000707000707010400000,
      0x2081111080110010110011001080000080700070710070700000000070700070
    ]
  | 2 => #[
      0x7070007071007070000000007071007070007170100000008071007071007170,
      0x7100717010811110808800101100880080800010807000707100707000000000,
      0x100000070700070710070701000000080880170711088888188118080710070,
      0x7070007070007070000000000000000000000000000000008070008088007070,
      0x7000707000000000707000707300707000000000707000707000707030000000,
      0x100000070700070700070700000000000000000000000000000000080700070,
      0x8070007070007070008000008070008088007070000000007070007070007070,
      0x800081800000800000000000000000800000800000000000000000000000,
      0x1010000080000000000000000020000080000080888080008080000080000000,
      0x7070007070007071101000107070007070007070004000008000101011101000,
      0x1110100010800000807000707000707000000000707000707111707010101110,
      0x1100000070700070710070701000000080700070711170702081111080000010,
      0x8000001011008000808000008070007070007070000000007070007071007071,
      0x7100707000000000807000707100807281801180807000707100707010801110,
      0x1080111080000080888080008180000080700070700070700000000070700070,
      0x8071008188888071818088818070007071008071818011808070007071117071,
      0x7000707000000000800000000000000000000000807000707100707000000000,
      0x70700070730070700000000070700070700070700000000070700070,
      0x8811811141111111118111118111111114111111111111118070007070007070,
      0x8881883181811311811111818881811181811111818811611111881181811111,
      0x1111111171711171711171711141111181111111111111111111111188888381,
      0x8871817171117171118111117171117181117171111111117171117171117171,
      0x7111717111111111887181717111717121811111881181111111111111811111,
      0x8181111183881171711188718111111171711181711171711111111171711171,
      0x8188117171118872818811818171117171117171118111118188111111118811,
      0x8881811181811111817131818811717111111111817111717111717111111111,
      0x8181888181711171711181718181118181711171711171711181111181111181,
      0x8888818188818811818111118171117171117171115111118171118188888171,
      0x8888817181818881818811817111887181881181887181718111717111811111,
      0x40000000000000000000000088888881888888818188888181711181,
      0x3000000000000000000000000000000000000000000000000000000,
      0x800000000000000000100000800000000000000000000000,
      0x80000000000000300000000000000000000000000000000000000000000000,
      0x8800800000000000008000108000000000000000000000008800800000000000,
      0x880080000000000000300000000000000000000000000000000000000000,
      0x8180000080000000000000000080000080000000000000000000000080880000,
      0x8000008088000000000000005000000000000000000000008088000000008800,
      0x800080800000800000000000000000800000800000000000000000000000,
      0x80000000000000000000000080000080888080008080000080000000,
      0x8088002000008800808000008800800020000000008000008000000002000000,
      0x800000000000000888882808880882080800200800000808880800080800000,
      0x8080000080880080000088008080000088008000800000000080000080000000,
      0x8000000000000000000000008888888088808880808008008000008088808000,
      0x8000707000000000707000707000707000000000707000707000707000400000,
      0x2080000088008000000000000080000088708070700070700080000070700070,
      0x7070008070007070000000007070007070007070000000008870807070007070,
      0x7000707000800000808800000000880080800000888800707000887080000000,
      0x80700070700070700000000080880070700088728088008080700070,
      0x8070007070007070008000008000008088808000808000008070808088007070,
      0x7000707000800000807000808888807080808880807000707000807080800080,
      0x8088008088708070800070700080000088888080888088008080000080700070,
      0x8888888088888880808888808070008088888070808088808088008070008870,
      0x320020200000420020000000000000300000400000000000000000000000,
      0x2020020083323030322032002030000050000030322030002020000040320000,
      0x7272007070007270202200207270207070007070004000008222222022202220,
      0x887282707222727020822220707020707222707020202220,
      0x80700080700070704000000083703070700070700080000040000000,
      0x200000000000000000000008073008070007370400000008070008070007070,
      0x7000707000000000807200807200727040000000707200707000727020320020,
      0x2030222000002000000000000000000080700080720070700000000080700080,
      0x8070008072007072220000008070008070007070300000007070007072227070,
      0x7222727020822220000000000000000000200000807000807000707000000000,
      0x8200000080700080720070722200000080720080700072704000000088728270,
      0x4300300000000000003000004000000000000000001000008288008072008872
    ]
  | 3 => #[
      0x3200330030000000300000303200300020000000303200000000320020000000,
      0x2000000088708070700070700080000088228020222022002080000038330030,
      0x8088007072008870800000007070007072007070200000007072007070007270,
      0x7000817080100000887181717111717010811111411110101110110010100000,
      0x80880080710088718100001080700080710070711101000080710080,
      0x8073008070007370400000007070007070007070003000000000000000000000,
      0x807000807300707000000000807000807100707000000000,
      0x80700080710070713100000070700070700070700001000000000000,
      0x8070008070007070000000008070008072007070,
      0x7200707000000000808800807100887181000000707000707000707000000030,
      0x30001040000000000000000000000080801080880070700000000080700080,
      0x3000003032000000000000003033000000003300303000003000000000000000,
      0x7000707010800000828800202200880080800000300080303300000000000000,
      0x70700070720070700000000080880070700088708088008080700070,
      0x8071007071007170108111102011001011001100101000008070008088007070,
      0x7100707000000000807000807100707000000000807100807000717040000000,
      0x8111111080880070710088708088118010110010110011001010001080700080,
      0x8070008088007070010000008070008071007070100000008088018088108871,
      0x7000707030000000707000707000707000000000000000000000000000000000,
      0x80700080700070700000000080700080730070700000000080700080,
      0x8070008070007070010000007070007070007070000000000000000000000000,
      0x807000807000807000100000807000808800707000000000,
      0x3030000030000000000030003130000030000000000000000030000050000000,
      0x8000208088808000808000003000000000000000008000003000003033303000,
      0x8888807080808880807000707000807180800080807000707000707000800000,
      0x1081111020000010111010001010000080700070700070700000000080700080,
      0x8070008071007071110000008070008071007070400000008070007071117070,
      0x7100807080801180100000101100100010100000807000807000707000000000,
      0x80700080710070700000000080700080720080718110111080700070,
      0x8070008088888071808088801000001011101000111000008070008070007070,
      0x7100707000000000807100818811808888101111807000807100807181101110,
      0x80700070700070700000000010000000000000000000000080700080,
      0x8070008070007070000000008070008073007070000000008070008070007070,
      0x1111331131511111331131111111111111511111811111111111111111111111,
      0x8181121133333131333133113151111131111131333131113151111131331111,
      0x8288117171118871818811818871817171117171118111118888828188818821,
      0x1111111111111111888888818888887181888881817121818888817181818881,
      0x1111111181711181711171714111111188718171711171711181111121111111,
      0x1211111111111111111111118188118171118871811111118171118171117171,
      0x7111717111111111818811817211887181111111818811717111887181881181,
      0x8181888111112111111111111111111181711181881171711111111181711181,
      0x8171118188118188881111118171118171118171811111118171118188888171,
      0x8888887181888881111111111111111111511111817111817111717111111111,
      0x8811111181711181881181888811111181881181711188718111111188888881,
      0x8000000000000000000000008888118188118888,
      0x300000000000000000000000000000000000000,
      0x80000000000000000020000080000000,
      0x8800800000000000008000000000000030000000000000000000000000000000,
      0x880080000000000000800010400000000000000000000000,
      0x80880000000088008000000000000030000000000000000000000000,
      0x8088000000008800811000008000000000000000008000001000000000000000,
      0x800000808800000000000000500000000000000000000000,
      0x8010000080000000000080008010000080000000000000000080000010000000,
      0x1000000001000000000000008000000000000000000000008000008088108000,
      0x8810800080100000808800200000880080100000880080002000000000800000,
      0x80000080000000010000000000000088881180881088208010010080000080,
      0x8000008088808000808000008088001000008800808000008800800010000000,
      0x7000707000400000800000000000000000000000888881808880881080800100,
      0x80000070700070700070700000000070700070700070700000000070700070,
      0x8870807070007070108000004100100000000000001000008870807070007070,
      0x7000887080000000707000707000707000000000707000707000707000000000,
      0x8011001080700070700070700080000010110000000011001010000081880070,
      0x8070108088007070000000007070007070007070000000008088007070008871,
      0x7000807080100010807000707000707000800000100000101110100010100000
    ]
  | 4 => #[
      0x1050000080700070700070700010000080700080881180708010111080700070,
      0x8088007070008870801100108870807070007070008000001111101011101100,
      0x828811808811887080111110807000808811807080101110,
      0x8080000080880000000088008080000088008000000000000080000080000000,
      0x8888888088808880808008008888808088808800808000008000008088808000,
      0x8888807080808880888800807000887080880080887080708000707000800000,
      0x80000080000000000000000000000088888880888888808088888080708080,
      0x8070008070007070000000008070008070007070400000008870807070007070,
      0x7000887080880080080000000000000000000000808800807000887080000000,
      0x80700080700070700000000080880080720088708000000080880070,
      0x8070008088888070808088800000800000000000000000008080008088007070,
      0x7000807000000000807000808800808888000000807000807000807080000000,
      0x8000000088888880888888708088888000000000000000000080000080700080,
      0x8288008088008888880000008070008088008088880000008088008070008870,
      0x320030000000430030000000000000300000400000000000000000200000,
      0x2020000032330030320033003000000030000030320030002000000030320000,
      0x7072007070007270300000007470407070007070004000008222202022202200,
      0x2220220020200000807300707200737030000000707000707200707020000000,
      0x2202000080720080700072704020000088728272722272702082222242222020,
      0x8088008072008872820000208070008072007072,
      0x7400707000000000807300807000837080000000707000707000707000300000,
      0x2000000000000000000000000000080700080740070700000000080700080,
      0x8070008074007070000000008070008072007072320000007070007070007070,
      0x7000707000000020000000000000000000000000807000807000707000000000,
      0x80700080740070700000000080880080720088728200000070700070,
      0x3000000000000000003000102000000000000000000000008070208088007070,
      0x3300000000000000300000303200000000000000303300000000330030100000,
      0x3011001070700070700070701040000028220020220022002020000030001030,
      0x7080007073007070000000007070007072007070000000007073007070007370,
      0x7000887080000000808800707200887080882280202200202200220020200000,
      0x1010001080700080880070700000000080700080720070700000000080880080,
      0x8088018071108871811111107071007071007170103111101011001011001100,
      0x807000808800707001000000807000808800707010000000,
      0x80700080700070703000000070700070700070700000000000000000,
      0x8070008070007070000000008070008074007070,
      0x8800707000000000807000807000707003000000707000707000707000000000,
      0x30000020000000000000000000000080700080700070700010000080700080,
      0x3000003033103000301000003000000000003000311000003000000000000000,
      0x7000707000400000200080202220200020200000300000000000000000100000,
      0x70700070731170703010111070700070700070713010001070700070,
      0x8070008088888070808288802000002022202000202000007070007070008070,
      0x7000707000000000807000808800808888000000807000807100807080000000,
      0x8110111070700070710070701020111010000010110010001010000080700080,
      0x8070008070007070000000008070008074007070000000008070008071008071,
      0x8800808888101110707000707111707110101110100000101110100011100000,
      0x80700080710070700000000080710081881170711110111180700080,
      0x8070008070007070000000007070007070007070000000001000000000000000,
      0x1111111111511111807000807000707000000000807000807300707000000000,
      0x3111111131331111111133113111111133113111111111111151111121111111,
      0x2222212122212211218111113333113133113311311111113111113133113111,
      0x7311717131111111717311717111737131111111847141717111717111511111,
      0x8188888222222121222122112151111171731171731173713111111171711171,
      0x8171118188118188881211118188118171118871812111118888888288888871,
      0x7111717111211111111111111111111111111111818811818811888888111121,
      0x1111111181711181741171711111111181881181711188718111111171711171,
      0x7171117171117171111211111111111111111111111111118171118188117171,
      0x7111717111111111817111818811717111111111817111818811818888111111,
      0x8811111171711171711171711111113111111111111111111111111181711181,
      0x8181818188117171111111118171118188117171111111118188118188118888,
      0x400000000000000000000000,
      0x80000080000000000000000000000000000000030000000000000000000000,
      0x8000000000000000,
      0x810010000000000000100000000000003000000000000000,
      0x88008000000000000080002080000000
    ]
  | 5 => #[
      0x1000000000000000000000008088000000008800800000000000003000000000,
      0x808800000000880081100000400000000000000000300000,
      0x10000010000000000000000000000080000080880000000000000050000000,
      0x8000008088102000101000008000000000008000801000004000000000000000,
      0x2000000000100000100000000100000000000000800000000000000000000000,
      0x1010010080000080881020001010000080880020000088008010000041001000,
      0x8800800010000000008000008000000001000000000000008121818088102120,
      0x8810881080100100800000808810800080100000808800100000880080100000,
      0x80700070700070700080000080000000000000000000000088881180,
      0x8170107070007070001000007070007070007070000000007070007070007070,
      0x7000707000000000887080707000707020800000880080000000000000800000,
      0x1010000081880070700088708000000070700070700070700000000070700070,
      0x8088007070008871801100107070007070007070003000001011000000001100,
      0x1110100010100000807010808800707000000000707000707000707000000000,
      0x1010111080700070700080708010001070700070700070700010000010000010,
      0x1111101011101100101000008070007070007070001000008070008088117070,
      0x8811707010101110808800707000887080110010717010707000707000100000,
      0x80000080000000000000000000000081812180881171701011111080700080,
      0x8000008088108000801000008088000000008800801000008800800000000000,
      0x7000707000800000888881808880881080800100828810808810880080100000,
      0x8011111080701080881180708010111081880070700088708011001088708070,
      0x8870807070007070008000004000000000000000000000008188118088118870,
      0x7000887080000000807000807000707000000000807000807000707040000000,
      0x8000000070710070700071701031001001000000000000000000000080880080,
      0x8070008088007070000000008070008070007070000000008088008071008870,
      0x7000807080000000707000707111707010101110000010000000000000000000,
      0x10000080700080700070700000000080700080880070711100000080700080,
      0x8088008070008870800000007171117071117170101111300000000000000000,
      0x800000817100808800717111000000807000808800707111000000,
      0x8000000080880000000088008000000088008000000000000080000080000000,
      0x8888808088808800808000008288008088008800800000008000008088008000,
      0x8800807080000000808800707000887080000000887080707000707000800000,
      0x8088888888888080888088008080000080880080880088708000000080700080,
      0x8080008088008088880800008088008070008870808000008888888888888880,
      0x7000707000800000000000000000000000000000808800808800888888000080,
      0x80700080740070700000000080880080700088708000000080700070,
      0x7080007070007070000800000000000000000000000000008070008088007070,
      0x7000707000000000807000808800707000000000807000808800808888000000,
      0x8800000070700070700080700000008000000000000000000000000080700080,
      0x8070208088007070000000008070008088007070000000008088008088008888,
      0x330030200000300000000000000000300020200000000000000000000000,
      0x2020000030002030330000000000000030000030330000000000000030330000,
      0x7073007070007370302200207070007070007070204000002222002022002200,
      0x2200220020200000707000707300707000000000707000707300707000000000,
      0x80740080700074704000000080720070720072702082222020220020,
      0x2022002022002200202000208070008073007070000000008070008073007070,
      0x7400707020000000808802807220887282222220707200707200727020322220,
      0x80700080880070700200000080700080,
      0x8070008088007070000000008070008070007070300000007070007070007070,
      0x7000707000000000000000000000000000000000807000807000707000000000,
      0x20000080700080880070700000000080700080700070700200000070700070,
      0x3000000000000000002000002000000000000000000000008070008070007070,
      0x100000300000303310100010100000300000000000300031200000,
      0x3020002070700070700070700020000020001020221020002020000030000000,
      0x7070007070007070000000007070007073117070101011107070007070007071,
      0x7100707040000000708000707211707020282220200000202210200020200000,
      0x2020000080700080700070700000000080700080730070711100000080700080,
      0x8070008088008088882022207070007072007070202022202000002022002000,
      0x1110100011100000807000807000707000000000807000808800707000000000,
      0x1110111180700080710070713110111070700070711170711010111010000010,
      0x1000000000000000000000008070008071007070000000008071008188117071,
      0x7300707000000000807000807000707000000000707000707000707000000000,
      0x1121113121111111111111111111111180700080700070700000000080700080,
      0x3111113133111111111111113133111111113311312111113111111111111111
    ]
  | 6 => #[
      0x7111717121211111222211212211221121211111311131313311111111111111,
      0x1111111171711171731171711111111171731171711173713122112171711171,
      0x7172117172118271212222812122112122112211212111117171117173117171,
      0x7311717111111111817111817311717111111111817411817111747141111111,
      0x8822222171721171721172712122223121221121221122112121112181711181,
      0x8171118188117171121111118171118188117171211111118188128188218888,
      0x7111717121111111717111717111717111111111111111111111111111111111,
      0x1111111181711181711171711111111181711181881171711111111181711181,
      0x8171118171117171131111117171117171117171111111111111111111111111,
      0x817111817111817111811111817111818811717111111111,
      0x40000000,
      0x8000000000000000002000008000000000000000000000000000000003000000,
      0x3000000000000000000000000000000000000000000000000000000000000000,
      0x80008080000000000000000000000081001000000000000010000000000000,
      0x3000000000000000000000000000000000000000008100100000000000,
      0x800000800000000000000000000000802100000000210010000000,
      0x50000000000000000000000080880000000088008280000080000000,
      0x4000000000000000001000001000000000000000000000008000008088000000,
      0x800000808810300010100000400000000000300030100000,
      0x1010000041001000200000000010000010000000010000000000000080000000,
      0x8121112021102120108001008000008088103000101000004021002000003100,
      0x880080800000810010001000000000800000800000000100000000000000,
      0x81118180881011101010010080000080881010001010000080880010,
      0x7070007070007070000000007070007070007070004000008000000000000000,
      0x800000817010707000707000100000707000707000707000000000,
      0x70700070700070700000000081701070700080708080000081001000,
      0x8088000000008800808000008171007070007170100000007070007070007070,
      0x7000707000000000808800707000887280880080807000707000707000800000,
      0x10000010000010111010001010000080701080880070700000000070700070,
      0x8070008088117070101011107070007070007070301000107070007070007070,
      0x7000707000100000111110101110110010100000807000707000707000100000,
      0x1021111080700080881170701010111070710070700071701011001071701070,
      0x8100100000000000008000008000000000000000000000008171117071118170,
      0x8810110010100000800000808810100010100000808800000000880080800000,
      0x8088008081701070700070700080000088881180881088108080010081112080,
      0x8181118088117170101111108070108088117070101011108188007070008870,
      0x7000807080000000817010707000707000800000400000000000000000000000,
      0x80710080700071701000000080700080700070700000000080700080,
      0x8088008072008870800000008088007070008870808800800100000000000000,
      0x807000808800707000000000807000807000707000000000,
      0x1100000080700080700070703000000070700070711170701010111000001000,
      0x1000008070008070007070000000008070008088007071,
      0x8800707111000000807100807000717010000000717111707111717010111110,
      0x80000080000000000000000010000081710080710071711100000080700080,
      0x8000008088001000100000008088000000008800800000008100100000000000,
      0x7000707000800000828810808810880080800000811100808800110010000000,
      0x1000000080700080880070701000000080880070700088708000000081701070,
      0x8188118188118870808888818188108088108800808000008071008088007170,
      0x8800717111000010807000808800707111010000808800807000887080100000,
      0x8000000070700070700070700030000000000000000000000000000080710080,
      0x8070008088007070000000008070008074007070000000008088008070008870,
      0x7100707131000000707000707000707000010000000000000000000000000000,
      0x80700080700070700000000080700080880070700000000080700080,
      0x8071008071007171130000007070007070007070000000100000000000000000,
      0x807010807100707000000000807000808800707000000000,
      0x80880000000088008080000080000000000000000080008080000000,
      0x8288008088008800808000008000208088000000000000008000008088000000,
      0x8800707000000000808800707000887080880080807000707000807080800000,
      0x8088888080880080880088008080000080700080880070700000000080700080,
      0x8070008088007070000000008088008070008870800000008088008088008870,
      0x8800887080888880808800808800880080800080807000808800707000000000,
      0x800000080700080880080708000000080880880888088888888888080880080,
      0x7070007070007070000000000000000000000000000000008070008088007080,
      0x7000707000000000807000808800707000000000807000807000807080000000
    ]
  | 7 => #[
      0x800000070700070700070700000000000000000000000000000000080700080,
      0x8070008070007070002000008070008088007070000000008070008070007080,
      0x300032200000300000000000000000200000200000000000000000000000,
      0x2020000040000000000000000020000030000030332030002020000030000000,
      0x7070007070007072302000207070007070007070002000002000202022202000,
      0x2220200020200000707000707000707000000000707000707322707020202220,
      0x2200000080700080720070704000000070700070722270702022222020000020,
      0x2000002022002000202000008070008070007070000000008070008073007072,
      0x7400707000000000807000807200807282202220707000707200707020202220,
      0x2020222020000020222020002220000080700080700070700000000080700080,
      0x8072008288227072222022228070008072007072322022207070007072227072,
      0x7000707000000000400000000000000000000000807000807200707000000000,
      0x80700080730070700000000080700080700070700000000070700070,
      0x3111111111111111112111112111111111111111111111118070008070007070,
      0x1111111111311111311111313321311121211111311111111111311123211111,
      0x2121112171711171711171711121111121112121222121112121111141111111,
      0x7171117171117171111111117171117173227171212122217171117171117172,
      0x7211717121111111717111717222717121222221211111212221211121211111,
      0x2121111181711181711171711111111181711181731171722211111181711181,
      0x8171118172117182282122217171117172117171212122212111112122112111,
      0x2221211122211111817111817111717111111111817111817411717111111111,
      0x2221222281711181721171722321222171711171722271722121222121111121,
      0x8111111111111111111111118171118172117171111111118172118288227172,
      0x7311717111111111817111817111717111111111817111717111717111111111,
      0x50000000000000000000000081711181711171711111111181711181,
      0x3000000000000000000000000000000000000000000000000000000,
      0x800000000000000000200000800000000000000000000000,
      0x10000000000000300000000000000000000000000000000000000000000000,
      0x8100100000000000008000208000000000000000000000008100100000000000,
      0x210010000000000000300000000000000000000000000000000000000000,
      0x8880000080000000000000000080000080000000000000000000000080210000,
      0x8000002021000000000000005000000000000000000000008021000000008100,
      0x800080800000800000000000000000800000800000000000000000000000,
      0x80000000000000000000000080000080888080008080000080000000,
      0x4031003000003100101000004100100030000000001000008000000001000000,
      0x100000000000000813111303110313010100100500000303310300010100000,
      0x8080000080110010000081008080000081001000100000000080000080000000,
      0x8000000000000000000000008111111011101110108001008000008088808000,
      0x7000707000000000707000707000707000000000707000707000707000400000,
      0x2080000081001000000000000080000081701070700070700010000070700070,
      0x7070007070007070000000007070007070007070000000008170107070007070,
      0x7000707000800000801100000000810080800000817100707000717010000000,
      0x70700070700070700000000080710070700081888081008080700070,
      0x8070007070007070008000008000008088808000808000008070107071007070,
      0x7000707000100000807000808888807080808880807000707000807080800080,
      0x1011001081701070700070700010000041111010111011001010000080700070,
      0x8171117071117170101111107070007073117070101011107071007070007170,
      0x810080800000810010000000000000800000800000000000000000000000,
      0x8080010081111010111011001020000080000080888080008080000080110000,
      0x8171007070008170808100808170107070007070008000008111818088808110,
      0x817111707111817010111110807010808888807080808880,
      0x80700080700070704000000081701070700070700080000050000000,
      0x100000000000000000000008071008070007170100000008070008070007070,
      0x7000707000000000807100808800817080000000807100707000817080810080,
      0x8080888000001000000000000000000080700080710070700000000080700080,
      0x8070008088008088880000008070008070008070800000008070008088888070,
      0x7111717010111110000000000000000000100000807000807000707000000000,
      0x1100000080700080730070711100000080710080700071701000000071711170,
      0x8100100000000000008000008000000000000000001000008171008071007171,
      0x1100110010000000800000808800800080000000801100000000810080000000,
      0x8000000081701070700070700080000081112080888081008080000081110010,
      0x8071007071007170100000008070008088008070800000008071007070008170,
      0x7000817080100000818111818888817080888881811110808880810080800000,
      0x80710080710071711100001080700080880080888801000080710080
    ]
  | 8 => #[
      0x8071008070008170800000007070007070007070003000000000000000000000,
      0x807000807100707000000000807000808800707000000000,
      0x80700080880080888800000070700070700070700001000000000000,
      0x8070008070007070000000008070008088007070,
      0x7300707000000000807100807100717111000000707000707000707000000010,
      0x80001080000000000000000000000080701080710070700000000080700080,
      0x8000008088000000000000008011000000008100808000008000000000000000,
      0x7000707010800000811100808800810080800000800010101100000000000000,
      0x80700080880070700000000080710070700081708081008080700070,
      0x8071008088008170808288808011008088008100808000008070007071007070,
      0x7100707000000000807000808800707000000000807100807000817080000000,
      0x8881888080710080880081708081888080110080880081008080001080700080,
      0x8070008071007070010000008070008088007070100000008071018088108188,
      0x7000707030000000707000707000707000000000000000000000000000000000,
      0x80700080700070700000000080700080880070700000000080700080,
      0x8070008070007070010000007070007070007070000000000000000000000000,
      0x807000807000707000100000807000807300707000000000,
      0x8080000080000000000080008880000080000000000000000080000080000000,
      0x8000208088808000808000008000000000000000002000008000008088808000,
      0x8888807080808880807000707000808880800080807000707000707000800000,
      0x8082888080000080888080008080000080700070700070700000000080700080,
      0x8070008088008088880000008070008088008070800000008070008088888070,
      0x8800807080808880800000808800800080800000807000807000707000000000,
      0x80700080880070700000000080700080880080888880888080700080,
      0x8070008088888088808088808000008088808000888000008070008070007070,
      0x8800707000000000808800888888808888808888807000808800808888808880,
      0x70700070700070700000000040000000000000000000000080700080,
      0x8070008070007070000000008070008088007070000000008070008070007070,
      0x3222323222222222423222323222323222222222422222222222222222222222,
      0x2222222282322232322232322222222252322232332232322222222242322232,
      0x7272227272227272222222227272227272227272222222224222222222222222,
      0x2222222222222222827222727222727222222222727222727322727222222222,
      0x2222222282722282722272722222222272722272722272722222222242222222,
      0x4222222222222222222222228272228272227272222222228272228273227272,
      0x7422727222222222827222827222727222222222727222727222727222222222,
      0x2222222242222222222222222222222282722282722272722222222282722282,
      0x8272228288227272222222228272228272227272222222227272227272227272,
      0x7222727222222222422222222222222222222222827222827222727222222222,
      0x2222222282722282732272722222222282722282722272722222222272722272,
      0x8000000000000000000000008272228272227272,
      0x800000000000000000000000000000000000000,
      0x80000000000000000080000080000000,
      0x8800800000000000008000000000000080000000000000000000000000000000,
      0x880080000000000000800080800000000000000000000000,
      0x80880000000088008000000000000080000000000000000000000000,
      0x8088000000008800888000008000000000000000008000008000000000000000,
      0x800000808800000000000000800000000000000000000000,
      0x8080000080000000000080008080000080000000000000000080000080000000,
      0x8000000008000000000000008000000000000000000000008000008088808000,
      0x8880800080800000808800800000880080800000880080008000000000800000,
      0x80000080000000080000000000000088888880888088808080080080000080,
      0x8000008088808000808000008088008000008800808000008800800080000000,
      0x8000808000800000800000000000000000000000888888808880888080800800,
      0x80000080800080800080800000000080800080800080800000000080800080,
      0x8880808080008080808000008800800000000000008000008880808080008080,
      0x8000888080000000808000808000808000000000808000808000808000000000,
      0x8088008080800080800080800080000080880000000088008080000088880080,
      0x8080808088008080000000008080008080008080000000008088008080008888,
      0x8000808080800080808000808000808000800000800000808880800080800000,
      0x8080000080800080800080800080000080800080888880808080888080800080,
      0x8088008080008880808800808880808080008080008000008888808088808800,
      0x888888808888888080888880808000808888808080808880,
      0x8080000080880000000088008080000088008000000000000080000080000000,
      0x8888888088808880808008008888808088808800808000008000008088808000
    ]
  | 9 => #[
      0x8888808080808880888800808000888080880080888080808000808000800000,
      0x80000080000000000000000000000088888880888888808088888080808080,
      0x8080008080008080000000008080008080008080800000008880808080008080,
      0x8000888080880080080000000000000000000000808800808000888080000000,
      0x80800080800080800000000080880080880088808000000080880080,
      0x8080008088888080808088800000800000000000000000008080008088008080,
      0x8000808000000000808000808800808888000000808000808000808080000000,
      0x8000000088888880888888808088888000000000000000000080000080800080,
      0x8888008088008888880000008080008088008088880000008088008080008880,
      0x880080000000880080000000000000800000800000000000000000800000,
      0x8080000088880080880088008000000080000080880080008000000080880000,
      0x8088008080008880800000008880808080008080008000008888808088808800,
      0x8880880080800000808800808800888080000000808000808800808080000000,
      0x8808000080880080800088808080000088888888888888808088888888888080,
      0x8088008088008888880000808080008088008088,
      0x8800808000000000808800808000888080000000808000808000808000800000,
      0x8000000000000000000000000000080800080880080800000000080800080,
      0x8080008088008080000000008080008088008088880000008080008080008080,
      0x8000808000000080000000000000000000000000808000808000808000000000,
      0x80800080880080800000000080880080880088888800000080800080,
      0x8000000000000000008000808000000000000000000000008080808088008080,
      0x8800000000000000800000808800000000000000808800000000880080800000,
      0x8088008080800080800080808080000088880080880088008080000080008080,
      0x8080008088008080000000008080008088008080000000008088008080008880,
      0x8000888080000000808800808800888080888880808800808800880080800000,
      0x8080008080800080880080800000000080800080880080800000000080880080,
      0x8088088088808888888888808088008088008880808888808088008088008800,
      0x808000808800808008000000808000808800808080000000,
      0x80800080800080808000000080800080800080800000000000000000,
      0x8080008080008080000000008080008088008080,
      0x8800808000000000808000808000808008000000808000808000808000000000,
      0x80000080000000000000000000000080800080800080800080000080800080,
      0x8000008088808000808000008000000000008000888000008000000000000000,
      0x8000808000800000800080808880800080800000800000000000000000800000,
      0x80800080888880808080888080800080800080888080008080800080,
      0x8080008088888080808888808000008088808000808000008080008080008080,
      0x8000808000000000808000808800808888000000808000808800808080000000,
      0x8880888080800080880080808080888080000080880080008080000080800080,
      0x8080008080008080000000008080008088008080000000008080008088008088,
      0x8800808888808880808000808888808880808880800000808880800088800000,
      0x80800080880080800000000080880088888880888880888880800080,
      0x8080008080008080000000008080008080008080000000008000000000000000,
      0x8888888888888888808000808000808000000000808000808800808000000000,
      0x8888888888888888888888888888888888888888888888888888888888888888,
      0x8888888888888888888888888888888888888888888888888888888888888888,
      0x8888888888888888888888888888888888888888888888888888888888888888,
      0x8888888888888888888888888888888888888888888888888888888888888888,
      0x8888888888888888888888888888888888888888888888888888888888888888,
      0x8888888888888888888888888888888888888888888888888888888888888888,
      0x8888888888888888888888888888888888888888888888888888888888888888,
      0x8888888888888888888888888888888888888888888888888888888888888888,
      0x8888888888888888888888888888888888888888888888888888888888888888,
      0x8888888888888888888888888888888888888888888888888888888888888888,
      0x8888888888888888888888888888888888888888888888888888888888888888
    ]
  | _ => #[]

private def ntDeletionChoice (s : List ℕ) : ℕ :=
  let rank := ntLehmer s
  let word := (ntDeletionChoiceBlock (rank / 4096)).getD (rank / 64 % 64) 0
  (word >>> (4 * (rank % 64))) % 16

private def ntDeletionSliceOk (v : ℕ) (s : List ℕ) : Bool :=
  let full := ntInsertCodeZero v s
  let y := ntDeletionChoice full
  if y < 8 then ntDist7 (ntDeleteCode full y) < 15
  else !ntIsGB 8 (ntQuads 8) full

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in

/-- Deletion: every generic element is an insertion of a smaller generic one. -/
private lemma ntDeletion {k : ℕ} (hk : 6 ≤ k) {σ : Equiv.Perm (Fin (k + 2))}
    (hσ : σ ∈ ntG (k + 1)) :
    ∃ y : Fin (k + 2), ∃ ρ ∈ ntG k, σ = ntIns y (σ y) ρ := by
  by_cases h : k = 6
  · subst k
    have hvne : (σ 0).val ≠ 7 := by
      intro hv
      apply hσ.1.1
      apply Fin.ext
      simpa using hv
    have hvlt : (σ 0).val < 7 := by
      have := (σ 0).is_lt
      omega
    let v : Fin 7 := ⟨(σ 0).val, hvlt⟩
    obtain ⟨ρ, hσρ⟩ := ntIns_exists 0 (σ 0) σ rfl
    have hok := (List.all_eq_true.mp (ntDeletionCertificate v)) (ntCode ρ)
      (ntCode_mem_permutations' ρ)
    dsimp only [ntDeletionSliceOk] at hok
    have hfull : ntInsertCodeZero v.val (ntCode ρ) = ntCode σ := by
      rw [hσρ, ntCode_ins_zero]
    rw [hfull] at hok
    generalize hyval : ntDeletionChoice (ntCode σ) = y at hok
    by_cases hy : y < 8
    · rw [ite_eq_left hy] at hok
      have hdist : ntDist7 (ntDeleteCode (ntCode σ) y) < 15 := by
        simpa only [decide_eq_true_eq] using hok
      let Y : Fin 8 := ⟨y, hy⟩
      obtain ⟨τ, hστ⟩ := ntIns_exists Y (σ Y) σ rfl
      have hdelete : ntDeleteCode (ntCode σ) y = ntCode τ := by
        rw [hστ]
        exact ntDeleteCode_ins Y (σ Y) τ
      have hτdist : ntDist7 (ntCode τ) < 15 := by
        rwa [hdelete] at hdist
      exact ⟨Y, τ, ntDist7_lt_memG τ hτdist, hστ⟩
    · rw [ite_eq_right hy, ntIsGB_of_memG8 hσ] at hok
      simp at hok
  · exact ntDeletion_large (by omega) hσ

/-- Every generic element reaches a reference permutation. -/
private lemma ntG_two (m : ℕ) {σ : Equiv.Perm (Fin (m + 7))}
    (hσ : σ ∈ ntG (m + 6)) :
    Relation.EqvGen (ntMove (m + 7)) σ (ntEven (m + 7)) ∨
      Relation.EqvGen (ntMove (m + 7)) σ (ntOdd (m + 5)) := by
  induction m with
  | zero => exact ntSmall7 hσ
  | succ m IH =>
    have hE := hσ.1
    obtain ⟨y, ρ, hρ, heq⟩ := ntDeletion (k := m + 6) (by omega) hσ
    have hyv : (y ≠ 0 ∨ σ y ≠ Fin.last (m + 5 + 2)) ∧
        (y ≠ Fin.last (m + 5 + 2) ∨ σ y ≠ 0) := by
      constructor
      · by_cases hy : y = 0
        · refine Or.inr ?_
          intro hcon
          rw [hy] at hcon
          exact hE.1 hcon
        · exact Or.inl hy
      · by_cases hy : y = Fin.last (m + 5 + 2)
        · refine Or.inr ?_
          intro hcon
          rw [hy] at hcon
          exact hE.2 hcon
        · exact Or.inl hy
    have hIH : ∀ ρ ∈ ntG (m + 5 + 1),
        Relation.EqvGen (ntMove (m + 5 + 2)) ρ (ntEven (m + 5 + 2)) ∨
          Relation.EqvGen (ntMove (m + 5 + 2)) ρ (ntOdd (m + 5)) :=
      fun ρ hρ => IH hρ
    have hm55 : 5 ≤ m + 5 := by omega
    rw [heq]
    exact ntInsertion (m := m + 5) hm55 hIH hρ hyv

/-- The extreme-avoiding count is `n + 1`. -/
private lemma ntE_formula (m : ℕ) :
    ntncl (ntMove (m + 7)) (ntE (m + 6)) = m + 8 := by
  have hjpf : ∀ t : Fin (m + 6), t.val + 1 + 1 ≤ m + 7 := by
    intro t
    have ht := t.is_lt
    omega
  have hex : ∀ t : Fin (m + 6), ∃ hub ∈ ntK (m + 7) (t.val + 1) (hjpf t),
      ∀ κ ∈ ntK (m + 7) (t.val + 1) (hjpf t),
        Relation.EqvGen (ntMove (m + 7)) κ hub := by
    intro t
    have ht := t.is_lt
    exact ntK_hub (by omega) (by omega) (hjpf t)
  choose hub hhubmem hhubreach using hex
  have hsub : ∀ t : Fin (m + 6),
      ntK (m + 7) (t.val + 1) (hjpf t) ⊆ ntE (m + 6) := by
    intro t
    have ht := t.is_lt
    exact ntK_sub_E (by omega) (hjpf t)
  have hirr : ∀ a b : Equiv.Perm (Fin (m + 7)),
      ntMove (m + 7) a b → a ≠ b :=
    fun a b h => ntMove_ne h
  have hevenK : ∀ t : Fin (m + 6),
      ntEven (m + 7) ∉ ntK (m + 7) (t.val + 1) (hjpf t) := by
    intro t
    exact ntInc5_notK (k := m + 5) (by omega)
      (by have ht := t.is_lt; omega) (hjpf t) (ntEven_mem m).2.2
  have hoddK : ∀ t : Fin (m + 6),
      ntOdd (m + 5) ∉ ntK (m + 7) (t.val + 1) (hjpf t) := by
    intro t
    exact ntInc5_notK (k := m + 5) (by omega)
      (by have ht := t.is_lt; omega) (hjpf t) (ntOdd_mem m).2.2
  have hclosed : ∀ t : Fin (m + 6),
      ∀ x ∈ ntK (m + 7) (t.val + 1) (hjpf t), ∀ y : Equiv.Perm (Fin (m + 7)),
        (ntMove (m + 7) x y ∨ ntMove (m + 7) y x) →
          y ∈ ntK (m + 7) (t.val + 1) (hjpf t) := by
    intro t x hx y h
    have ht := t.is_lt
    exact ntK_closed (by omega) (by omega) (hjpf t) hx h
  refine ntNcl_eq_of_reps (x := fun k : Fin (m + 8) =>
    if h : k.val < m + 6 then hub ⟨k.val, h⟩
    else if _ : k.val = m + 6 then ntEven (m + 7) else ntOdd (m + 5)) ?_ ?_ ?_ ?_
  · intro k
    by_cases hk : k.val < m + 6
    · simp only [dite_eq_left hk]
      exact hsub ⟨k.val, hk⟩ (hhubmem _)
    · by_cases hk6 : k.val = m + 6
      · simp only [dite_eq_right hk, dite_eq_left hk6]
        exact (ntEven_mem m).1
      · simp only [dite_eq_right hk, dite_eq_right hk6]
        exact (ntOdd_mem m).1
  · intro k
    by_cases hk : k.val < m + 6
    · simp only [dite_eq_left hk]
      exact (ntNcl_nontrivial_iff hirr).mpr (ntPat_move (hhubmem _).2)
    · by_cases hk6 : k.val = m + 6
      · simp only [dite_eq_right hk, dite_eq_left hk6]
        exact (ntNcl_nontrivial_iff hirr).mpr (ntPat_move (ntEven_mem m).2.1)
      · simp only [dite_eq_right hk, dite_eq_right hk6]
        exact (ntNcl_nontrivial_iff hirr).mpr (ntPat_move (ntOdd_mem m).2.1)
  · intro k l hkl h
    have hsign_even : Equiv.Perm.sign (ntEven (m + 7)) = 1 := by
      unfold ntEven
      exact Equiv.Perm.sign_one
    have hsign_odd : Equiv.Perm.sign (ntOdd (m + 5)) = -1 := by
      unfold ntOdd
      apply Equiv.Perm.sign_swap
      intro hcon
      have e2 : m + 5 = m + 5 + 1 := congrArg Fin.val hcon
      omega
    by_cases hk : k.val < m + 6 <;> by_cases hl : l.val < m + 6
    · simp only [dite_eq_left hk, dite_eq_left hl] at h
      set t1 : Fin (m + 6) := ⟨k.val, hk⟩
      set t2 : Fin (m + 6) := ⟨l.val, hl⟩
      have hv1 : t1.val = k.val := rfl
      have hv2 : t2.val = l.val := rfl
      have ht12 : t1 ≠ t2 := by
        intro e
        apply hkl
        have e3 := congrArg Fin.val e
        exact Fin.ext (hv1.symm.trans (e3.trans hv2))
      have hj12 : t1.val + 1 ≠ t2.val + 1 := by
        intro e
        apply ht12
        apply Fin.ext
        omega
      have hdisj := ntK_disjoint (n := m + 7) (j := t1.val + 1) (k := t2.val + 1)
        (by omega) (by have h1 := t1.is_lt; omega) (hjpf t1)
        (by have h2 := t2.is_lt; omega) (hjpf t2) hj12
      have hmem1 : hub t2 ∈ ntK (m + 7) (t1.val + 1) (hjpf t1) :=
        (ntClosed_mem (hclosed t1) h).mp (hhubmem t1)
      exact Set.disjoint_left.mp hdisj hmem1 (hhubmem t2)
    · by_cases hl6 : l.val = m + 6
      · simp only [dite_eq_left hk, dite_eq_right hl, dite_eq_left hl6] at h
        set t1 : Fin (m + 6) := ⟨k.val, hk⟩
        have hmemE : ntEven (m + 7) ∈ ntK (m + 7) (t1.val + 1) (hjpf t1) :=
          (ntClosed_mem (hclosed t1) h).mp (hhubmem t1)
        exact hevenK t1 hmemE
      · simp only [dite_eq_left hk, dite_eq_right hl, dite_eq_right hl6] at h
        set t1 : Fin (m + 6) := ⟨k.val, hk⟩
        have hmemO : ntOdd (m + 5) ∈ ntK (m + 7) (t1.val + 1) (hjpf t1) :=
          (ntClosed_mem (hclosed t1) h).mp (hhubmem t1)
        exact hoddK t1 hmemO
    · by_cases hk6 : k.val = m + 6
      · simp only [dite_eq_right hk, dite_eq_left hk6, dite_eq_left hl] at h
        set t2 : Fin (m + 6) := ⟨l.val, hl⟩
        have h' : Relation.EqvGen (ntMove (m + 7)) (hub t2) (ntEven (m + 7)) :=
          Relation.EqvGen.symm _ _ h
        have hmemE : ntEven (m + 7) ∈ ntK (m + 7) (t2.val + 1) (hjpf t2) :=
          (ntClosed_mem (hclosed t2) h').mp (hhubmem t2)
        exact hevenK t2 hmemE
      · simp only [dite_eq_right hk, dite_eq_right hk6, dite_eq_left hl] at h
        set t2 : Fin (m + 6) := ⟨l.val, hl⟩
        have h' : Relation.EqvGen (ntMove (m + 7)) (hub t2) (ntOdd (m + 5)) :=
          Relation.EqvGen.symm _ _ h
        have hmemO : ntOdd (m + 5) ∈ ntK (m + 7) (t2.val + 1) (hjpf t2) :=
          (ntClosed_mem (hclosed t2) h').mp (hhubmem t2)
        exact hoddK t2 hmemO
    · by_cases hk6 : k.val = m + 6 <;> by_cases hl6 : l.val = m + 6
      · apply hkl
        apply Fin.ext
        omega
      · simp only [dite_eq_right hk, dite_eq_left hk6, dite_eq_right hl,
          dite_eq_right hl6] at h
        have hs := ntEqvGen_sign h
        rw [hsign_even, hsign_odd] at hs
        exact absurd hs (by decide)
      · simp only [dite_eq_right hk, dite_eq_right hk6, dite_eq_right hl,
          dite_eq_left hl6] at h
        have hs := ntEqvGen_sign h
        rw [hsign_odd, hsign_even] at hs
        exact absurd hs (by decide)
      · apply hkl
        apply Fin.ext
        have hkk := k.is_lt
        have hll := l.is_lt
        omega
  · intro z hzE hcardz
    obtain ⟨y, hy⟩ := (ntNcl_nontrivial_iff hirr).mp hcardz
    have hpat : ntPat (m + 7) z := ntMove_pat hy
    by_cases hex : ∃ t : Fin (m + 6), z ∈ ntK (m + 7) (t.val + 1) (hjpf t)
    · obtain ⟨t, hmem⟩ := hex
      have htk : t.val < m + 8 := by
        have ht := t.is_lt
        omega
      refine ⟨⟨t.val, htk⟩, ?_⟩
      have hlt : (⟨t.val, htk⟩ : Fin (m + 8)).val < m + 6 := t.is_lt
      simp only [dite_eq_left hlt]
      have hteq : (⟨(⟨t.val, htk⟩ : Fin (m + 8)).val, hlt⟩ : Fin (m + 6)) = t :=
        Fin.ext rfl
      rw [hteq]
      exact hhubreach t z hmem
    · have hzG : z ∈ ntG (m + 6) := by
        refine ⟨hzE, hpat, ?_⟩
        intro j hj hmem
        by_cases hj0 : j = 0
        · subst hj0
          rw [ntK_zero_empty hj] at hmem
          exact absurd hmem (Set.notMem_empty z)
        · obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
          have hjm : j' < m + 6 := by omega
          refine hex ⟨⟨j', hjm⟩, ?_⟩
          exact hmem
      rcases ntG_two m hzG with h | h
      · have htk : m + 6 < m + 8 := by omega
        refine ⟨⟨m + 6, htk⟩, ?_⟩
        have hval : ((⟨m + 6, htk⟩ : Fin (m + 8)).val) = m + 6 := rfl
        have hnlt : ¬ ((⟨m + 6, htk⟩ : Fin (m + 8)).val < m + 6) := by omega
        simp only [dite_eq_right hnlt]
        exact h
      · have htk : m + 7 < m + 8 := by omega
        refine ⟨⟨m + 7, htk⟩, ?_⟩
        have hval : ((⟨m + 7, htk⟩ : Fin (m + 8)).val) = m + 7 := rfl
        have hnlt : ¬ ((⟨m + 7, htk⟩ : Fin (m + 8)).val < m + 6) := by omega
        have hne6 : ¬ ((⟨m + 7, htk⟩ : Fin (m + 8)).val = m + 6) := by omega
        simp only [dite_eq_right hnlt, dite_eq_right hne6]
        exact h

/-- The class count equals the formula for all `n ≥ 5`. -/
private lemma ntCount_eq (k : ℕ) (hk : 5 ≤ k) :
    ntncl (ntMove k) Set.univ = (k ^ 3 + 6 * k ^ 2 - 55 * k + 54) / 6 := by
  obtain ⟨t, rfl⟩ : ∃ t, k = t + 5 := ⟨k - 5, by omega⟩
  have htwo : ∀ t, 6 * ntncl (ntMove (t + 5)) Set.univ =
      (t + 5) ^ 3 + 6 * (t + 5) ^ 2 - 55 * (t + 5) + 54 := by
    intro t
    induction t using Nat.twoStepInduction with
    | zero =>
      have h : 6 * ntncl (ntMove 5) Set.univ =
          5 ^ 3 + 6 * 5 ^ 2 - 55 * 5 + 54 := by
        norm_num [ntSmall5]
      exact h
    | one =>
      have h : 6 * ntncl (ntMove 6) Set.univ =
          6 ^ 3 + 6 * 6 ^ 2 - 55 * 6 + 54 := by
        norm_num [ntSmall6]
      exact h
    | more n ih1 ih2 =>
      have hrec := ntCount_recursion (n + 5)
      have he' : ntncl (ntMove (n + 5 + 2)) (ntE (n + 5 + 1)) = n + 8 :=
        ntE_formula n
      rw [he'] at hrec
      have hrec' : ntncl (ntMove (n + 7)) Set.univ +
          ntncl (ntMove (n + 5)) Set.univ =
          2 * ntncl (ntMove (n + 6)) Set.univ + (n + 8) := hrec
      have hgoal : 6 * ntncl (ntMove (n + 7)) Set.univ =
          (n + 7) ^ 3 + 6 * (n + 7) ^ 2 - 55 * (n + 7) + 54 := by
        have ih1Z : (6 : ℤ) * ((ntncl (ntMove (n + 5)) Set.univ : ℕ) : ℤ) =
            ((((n + 5) ^ 3 + 6 * (n + 5) ^ 2 - 55 * (n + 5) + 54 : ℕ)) : ℤ) := by
          exact_mod_cast ih1
        have ih2Z : (6 : ℤ) * ((ntncl (ntMove (n + 6)) Set.univ : ℕ) : ℤ) =
            ((((n + 6) ^ 3 + 6 * (n + 6) ^ 2 - 55 * (n + 6) + 54 : ℕ)) : ℤ) := by
          exact_mod_cast ih2
        have hrecZ : (6 : ℤ) * ((ntncl (ntMove (n + 7)) Set.univ : ℕ) : ℤ) =
            2 * (6 * ((ntncl (ntMove (n + 6)) Set.univ : ℕ) : ℤ)) -
              6 * ((ntncl (ntMove (n + 5)) Set.univ : ℕ) : ℤ) +
              6 * ((((n : ℕ) + 8 : ℕ)) : ℤ) := by
          have hZ : ((ntncl (ntMove (n + 7)) Set.univ : ℕ) : ℤ) +
              ((ntncl (ntMove (n + 5)) Set.univ : ℕ) : ℤ) =
              2 * ((ntncl (ntMove (n + 6)) Set.univ : ℕ) : ℤ) +
              ((((n : ℕ) + 8 : ℕ)) : ℤ) := by
            exact_mod_cast hrec'
          linarith
        rw [ih1Z, ih2Z] at hrecZ
        have hcast8 : ((((n : ℕ) + 8 : ℕ)) : ℤ) = ((n : ℕ) : ℤ) + 8 := by
          push_cast
          ring
        rw [hcast8] at hrecZ
        have h5 := ntNum_cast (n + 5) (by omega)
        have h6 := ntNum_cast (n + 6) (by omega)
        have h7 := ntNum_cast (n + 7) (by omega)
        rw [h5, h6] at hrecZ
        have hfin : (6 : ℤ) * ((ntncl (ntMove (n + 7)) Set.univ : ℕ) : ℤ) =
            ((((n + 7) ^ 3 + 6 * (n + 7) ^ 2 - 55 * (n + 7) + 54 : ℕ)) : ℤ) := by
          rw [hrecZ, h7]
          exact ntPoly_step n
        exact_mod_cast hfin
      exact hgoal
  have hP := htwo t
  omega

end MetaMathlibExt

namespace MetaMathlibExt

/-- For n ≥ 7, the number of nontrivial equivalence classes of S_n under the {1234,
3412}-equivalence is (n^3 + 6n^2 - 55n + 54)/6, conjectured by Ma and given by sequence A330395.
Source: Quinn Perian, Bella Xu, and Alexander Lu Zhang, "Counting the Nontrivial Equivalence Classes
of Sn Under {1234,3412}-Pattern-Replacement", Journal of Integer Sequences 23 (2020), Article
20.10.2, Theorem `thm:nontrivial`, lines 172-175,
<https://cs.uwaterloo.ca/journals/JIS/VOL23/Zhang/zhang6.tex>.

Proof: Decompose the exceptional set into swap classes and a generic part. Kernel-checked
finite certificates handle the `S₅`/`S₆` classes, `S₇` reachability, and the `S₈` deletion
boundary. Point insertion then gives the recurrence, whose solution is the displayed polynomial.

Proves `Wanted` entry `card_nontrivial_1234_3412_classes`.
-/
theorem card_nontrivial_1234_3412_classes :
    ∀ (n : ℕ), 7 ≤ n →
      let OneMove : Equiv.Perm (Fin n) → Equiv.Perm (Fin n) → Prop :=
        fun σ τ => ∃ i1 i2 i3 i4 : Fin n,
          i1.val < i2.val ∧ i2.val < i3.val ∧ i3.val < i4.val ∧
            σ i1 < σ i2 ∧ σ i2 < σ i3 ∧ σ i3 < σ i4 ∧
            τ i1 = σ i3 ∧ τ i2 = σ i4 ∧ τ i3 = σ i1 ∧ τ i4 = σ i2 ∧
            ∀ j : Fin n, j ≠ i1 → j ≠ i2 → j ≠ i3 → j ≠ i4 → τ j = σ j;
      Nat.card { C : Set (Equiv.Perm (Fin n)) //
          ∃ σ, C = { τ | Relation.EqvGen OneMove σ τ } ∧ 1 < Nat.card ↥C } =
        (n ^ 3 + 6 * n ^ 2 - 55 * n + 54) / 6 := by
  intro n hn
  have hequiv : Nat.card { C : Set (Equiv.Perm (Fin n)) //
        ∃ σ, C = { τ | Relation.EqvGen (ntMove n) σ τ } ∧ 1 < Nat.card ↥C } =
      ntncl (ntMove n) Set.univ :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun C => by
      constructor
      · rintro ⟨σ, hC, hcard⟩
        exact ⟨σ, Set.mem_univ σ, hC, hcard⟩
      · rintro ⟨σ, -, hC, hcard⟩
        exact ⟨σ, hC, hcard⟩))
  have hfin : ntncl (ntMove n) Set.univ =
      (n ^ 3 + 6 * n ^ 2 - 55 * n + 54) / 6 :=
    ntCount_eq n (by omega)
  exact hequiv.trans hfin

end MetaMathlibExt
