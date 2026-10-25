/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WreathOrbits.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Instance.v1.Atlas.AlgebraicCombinatorics.code.YoungLattice.Part3
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.YoungLattice
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Finset.Card
import Mathlib.Order.Fin.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Data.List.Sort
import Mathlib.Data.List.FinRange
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.GetD
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Logic.Equiv.Basic
import Def.v1.Atlas.AlgebraicCombinatorics.code.WreathOrbits.Part3
set_option autoImplicit false


namespace WreathOrbits

variable {m n : ℕ}

lemma mem_rowCols_iff (S : Finset (Fin m × Fin n)) (i : Fin m) (j : Fin n) :
    j ∈ rowCols S i ↔ (i, j) ∈ S := by
  constructor
  · intro hj
    simp only [rowCols, Finset.mem_image, Finset.mem_filter] at hj
    obtain ⟨⟨a, b⟩, ⟨hab, ha_eq⟩, hb_eq⟩ := hj
    simpa [← ha_eq, ← hb_eq] using hab
  · intro hj
    simp only [rowCols, Finset.mem_image, Finset.mem_filter]
    exact ⟨(i, j), ⟨hj, rfl⟩, rfl⟩

lemma rowCols_card (S : Finset (Fin m × Fin n)) (i : Fin m) :
    (rowCols S i).card = rowSize S i := by
  simp only [rowCols, rowSize]
  rw [Finset.card_image_of_injOn]
  intro ⟨a₁, b₁⟩ h₁ ⟨a₂, b₂⟩ h₂ heq
  exact Prod.ext (by rw [(Finset.mem_filter.mp h₁).2, (Finset.mem_filter.mp h₂).2]) heq

lemma exists_perm_image_eq (A B : Finset (Fin n)) (h : A.card = B.card) :
    ∃ σ : Equiv.Perm (Fin n), A.image σ = B := by
  classical
  let e' : {x : Fin n // x ∈ A} ≃ {x : Fin n // x ∈ B} := Finset.equivOfCardEq h
  refine ⟨e'.extendSubtype, ?_⟩
  ext x
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact Equiv.extendSubtype_mem e' a ha
  · intro hx
    refine ⟨(e'.symm ⟨x, hx⟩).val, (e'.symm ⟨x, hx⟩).prop, ?_⟩
    rw [Equiv.extendSubtype_apply_of_mem e' _ (e'.symm ⟨x, hx⟩).prop]
    simp

lemma fiber_card_eq (S T : Finset (Fin m × Fin n))
    (h : rowSizeMultiset S = rowSizeMultiset T) (v : ℕ) :
    Fintype.card {i : Fin m // rowSize S i = v} =
    Fintype.card {i : Fin m // rowSize T i = v} := by
  suffices key : ∀ (f : Fin m → ℕ),
      Fintype.card {i : Fin m // f i = v} =
      Multiset.count v (Finset.univ.val.map f) by
    rw [key, key]; exact congr_arg _ h
  intro f
  rw [Fintype.card_subtype, Multiset.count_map,
      show Multiset.filter (fun a => v = f a) Finset.univ.val =
           (Finset.univ.filter (fun a => v = f a)).val from rfl,
      Finset.card_val]
  congr 1; ext x; simp [eq_comm]

lemma rowSizeMultiset_eq_of_sameOrbit (S T : Finset (Fin m × Fin n))
    (h : SameOrbit S T) : rowSizeMultiset S = rowSizeMultiset T := by
  obtain ⟨g, rfl⟩ := h
  simp only [rowSizeMultiset]
  conv_rhs =>
    rw [show Finset.univ.val.map (rowSize (g.actOnSet S)) =
      (Finset.univ.val.map g.σ.symm).map (rowSize S) from by
        rw [Multiset.map_map]; congr 1; ext i
        simp only [Function.comp, ← rowSize_actOnSet g S (g.σ.symm i), Equiv.apply_symm_apply]]
  congr 1; ext x; simp

lemma sameOrbit_of_rowSizeMultiset_eq (S T : Finset (Fin m × Fin n))
    (h : rowSizeMultiset S = rowSizeMultiset T) : SameOrbit S T := by
  classical

  let σ : Equiv.Perm (Fin m) := Equiv.ofFiberEquiv (f := rowSize S) (g := rowSize T)
    (fun v => Fintype.equivOfCardEq (fiber_card_eq S T h v))
  have hσ : ∀ i, rowSize S i = rowSize T (σ i) :=
    fun i => (Equiv.ofFiberEquiv_map _ i).symm

  have hrow_eq : ∀ i, (rowCols S i).card = (rowCols T (σ i)).card := by
    intro i; rw [rowCols_card, rowCols_card, hσ]
  choose τ hτ using fun i => exists_perm_image_eq _ _ (hrow_eq i)

  refine ⟨⟨σ, τ⟩, ?_⟩
  ext ⟨a, b⟩
  simp only [WreathElem.actOnSet, Finset.mem_image, WreathElem.actOn, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨i, j⟩, hij, rfl, rfl⟩
    exact (mem_rowCols_iff T (σ i) (τ i j)).mp
      (by rw [← hτ i]; exact Finset.mem_image_of_mem _ ((mem_rowCols_iff S i j).mpr hij))
  · intro hab
    let i := σ.symm a
    have hi : σ i = a := Equiv.apply_symm_apply σ a
    have hb : b ∈ (rowCols S i).image (τ i) := by
      rw [hτ, hi]; exact (mem_rowCols_iff T a b).mpr hab
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
    exact ⟨⟨i, j⟩, (mem_rowCols_iff S i j).mp hj, hi, rfl⟩

theorem sameOrbit_iff_rowSizeMultiset_eq (S T : Finset (Fin m × Fin n)) :
    SameOrbit S T ↔ rowSizeMultiset S = rowSizeMultiset T :=
  ⟨rowSizeMultiset_eq_of_sameOrbit S T, sameOrbit_of_rowSizeMultiset_eq S T⟩

lemma rowSize_le (S : Finset (Fin m × Fin n)) (i : Fin m) : rowSize S i ≤ n := by
  unfold rowSize
  calc (S.filter (fun p => p.1 = i)).card
      ≤ (Finset.univ.filter (fun p : Fin m × Fin n => p.1 = i)).card := by
        apply Finset.card_le_card; intro x hx; simp [Finset.mem_filter] at hx ⊢; exact hx.2
    _ = n := by
        have : (Finset.univ.filter (fun p : Fin m × Fin n => p.1 = i)) =
               (Finset.univ : Finset (Fin n)).map
                 ⟨fun j => (i, j), fun a b h => by simp at h; exact h⟩ := by
          ext ⟨a, b⟩; simp [Finset.mem_filter, Finset.mem_map]; exact eq_comm
        rw [this, Finset.card_map, Finset.card_fin]

end WreathOrbits
