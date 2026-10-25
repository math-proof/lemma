/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section11.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicTopologyI.code.Section1.Part3
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section1
import Mathlib.Topology.Basic
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Algebra.Exact
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.Algebra.Module.Prod
import Def.v1.Atlas.AlgebraicTopologyI.code.Section11.Part4
open Set Topology

universe u

variable {X : Type*} [TopologicalSpace X]


namespace MayerVietoris

open Function

/-- Exactness at the middle term `C × A'` in the Mayer–Vietoris–style sequence of
Lemma 11.6. Given two horizontal exact sequences related by a ladder of vertical maps with
the indicated commutation properties, the composite
`c' ↦ (h c', −k' c')` followed by `(c, a') ↦ k c + f a'` is exact at `C × A'`. -/
theorem exact_at_prod
    {A B C A' B' C' Bprev Bprev' : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup C']
    [AddCommGroup Bprev] [AddCommGroup Bprev']
    (k : C →+ A) (j : A →+ B)
    (k' : C' →+ A') (j' : A' →+ B')
    (h : C' →+ C) (f : A' →+ A) (g : B' ≃+ B)
    (dprev : Bprev →+ C) (d'prev : Bprev' →+ C')
    (gprev : Bprev' ≃+ Bprev)
    (exact_A_top : Exact k j)
    (exact_A'_bot : Exact k' j')
    (exact_C_top : Exact dprev k)
    (exact_C'_bot : Exact d'prev k')
    (comm1 : ∀ x, k (h x) = f (k' x))
    (comm2 : ∀ x, j (f x) = g (j' x))
    (comm_prev : ∀ x, dprev (gprev x) = h (d'prev x)) :
    Exact
      (fun x : C' => (h x, -k' x) : C' → C × A')
      (fun p : C × A' => k p.1 + f p.2 : C × A' → A) := by
  intro ⟨c, a'⟩
  simp only
  constructor
  · intro heq
    have hjkc : j (k c) = 0 := by rw [exact_A_top]; exact ⟨c, rfl⟩
    have hjfa : j (f a') = 0 := by
      have := congr_arg j heq
      rw [map_add, hjkc, zero_add, map_zero] at this
      exact this
    have hj'a : j' a' = 0 := by
      have hgj' := (comm2 a').symm
      rw [hjfa] at hgj'
      exact g.injective (hgj'.trans (map_zero g).symm)
    rw [exact_A'_bot] at hj'a
    obtain ⟨y, hy⟩ := hj'a
    have hkc_eq : k (c + h y) = 0 := by rw [map_add, comm1, hy, heq]
    rw [exact_C_top] at hkc_eq
    obtain ⟨b, hb⟩ := hkc_eq
    have hb' : h (d'prev (gprev.symm b)) = c + h y := by
      rw [← comm_prev, AddEquiv.apply_symm_apply]; exact hb
    have hk'z : k' (d'prev (gprev.symm b)) = 0 := by
      rw [exact_C'_bot]; exact ⟨gprev.symm b, rfl⟩
    refine ⟨d'prev (gprev.symm b) - y, ?_⟩
    refine Prod.ext ?_ ?_
    · show h (d'prev (gprev.symm b) - y) = c
      rw [map_sub, hb']
      exact add_sub_cancel_right c (h y)
    · show -(k' (d'prev (gprev.symm b) - y)) = a'
      rw [map_sub, hk'z, zero_sub, neg_neg]
      exact hy
  · rintro ⟨x, hx⟩
    have h1 : h x = c := congr_arg Prod.fst hx
    have h2 : -k' x = a' := congr_arg Prod.snd hx
    rw [← h1, ← h2, map_neg, comm1, add_neg_cancel]

/-- Exactness at the term `A` of the Mayer–Vietoris–style sequence: the composite
`(c, a') ↦ k c + f a'` followed by the connecting map `a ↦ d'(g⁻¹(j a))` is exact at `A`. -/
theorem exact_at_A
    {A B C A' B' C₂' : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup C₂']
    (k : C →+ A) (j : A →+ B)
    (j' : A' →+ B') (d' : B' →+ C₂')
    (f : A' →+ A) (g : B' ≃+ B)
    (exact_A_top : Exact k j)
    (exact_B'_bot : Exact j' d')
    (comm2 : ∀ x, j (f x) = g (j' x)) :
    Exact
      (fun p : C × A' => k p.1 + f p.2)
      (fun a : A => d' (g.symm (j a))) := by
  intro a
  constructor
  · intro ha
    rw [exact_B'_bot (g.symm (j a))] at ha
    obtain ⟨a', ha'⟩ := ha
    have hja : j a = g (j' a') := by rw [ha']; exact (g.apply_symm_apply _).symm
    rw [← comm2 a'] at hja
    have hsub : j (a - f a') = 0 := by rw [map_sub, hja, sub_self]
    rw [exact_A_top] at hsub
    obtain ⟨c, hc⟩ := hsub
    refine ⟨(c, a'), ?_⟩
    show k c + f a' = a
    rw [hc]
    exact sub_add_cancel a (f a')
  · rintro ⟨⟨c, a'⟩, rfl⟩
    show d' (g.symm (j (k c + f a'))) = 0
    have hkc : j (k c) = 0 := by rw [exact_A_top]; exact ⟨c, rfl⟩
    have hd'j' : d' (j' a') = 0 := by rw [exact_B'_bot]; exact ⟨a', rfl⟩
    calc d' (g.symm (j (k c + f a')))
        = d' (g.symm (j (k c) + j (f a'))) := by rw [map_add]
      _ = d' (g.symm (0 + j (f a'))) := by rw [hkc]
      _ = d' (g.symm (j (f a'))) := by rw [zero_add]
      _ = d' (g.symm (g (j' a'))) := by rw [comm2]
      _ = d' (j' a') := by rw [g.symm_apply_apply]
      _ = 0 := hd'j'

/-- Exactness at the term `C'` of the Mayer–Vietoris–style sequence: the connecting map
`a ↦ d'(g⁻¹(j a))` followed by `c' ↦ (h c', −k' c')` is exact at `C'`. -/
theorem exact_at_C'
    {A B C A' B' C' : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup C']
    (j : A →+ B) (dtop : B →+ C)
    (k' : C' →+ A') (d' : B' →+ C')
    (h : C' →+ C) (g : B' ≃+ B)
    (exact_B_top : Exact j dtop)
    (exact_C'_bot : Exact d' k')
    (comm3 : ∀ x, dtop (g x) = h (d' x)) :
    Exact
      (fun a : A => d' (g.symm (j a)))
      (fun x : C' => (h x, -k' x) : C' → C × A') := by
  intro x
  simp only [Prod.mk_eq_zero, neg_eq_zero]
  constructor
  · intro ⟨hx1, hx2⟩
    rw [exact_C'_bot] at hx2
    obtain ⟨b', hb'⟩ := hx2
    have hdtop : dtop (g b') = 0 := by rw [comm3, hb', hx1]
    rw [exact_B_top] at hdtop
    obtain ⟨a, ha⟩ := hdtop
    have hgsym : g.symm (j a) = b' := by rw [ha]; exact g.symm_apply_apply b'
    exact ⟨a, by show d' (g.symm (j a)) = x; rw [hgsym, hb']⟩
  · rintro ⟨a, ha⟩
    have ha' : d' (g.symm (j a)) = x := ha
    constructor
    · rw [← ha', ← comm3, g.apply_symm_apply]
      rw [exact_B_top]; exact ⟨a, rfl⟩
    · rw [← ha', exact_C'_bot]; exact ⟨g.symm (j a), rfl⟩

end MayerVietoris
