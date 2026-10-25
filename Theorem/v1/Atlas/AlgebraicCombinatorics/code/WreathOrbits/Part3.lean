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
import Def.v1.Atlas.AlgebraicCombinatorics.code.WreathOrbits.Part4
set_option autoImplicit false


namespace WreathOrbits

variable {m n : ℕ}

lemma mem_iff_lt_rowSize {S : Finset (Fin m × Fin n)} (hS : IsLeftJustified S)
    (i : Fin m) (j : Fin n) : (i, j) ∈ S ↔ j.val < rowSize S i := by
  unfold rowSize
  set Ri := S.filter (fun p => p.1 = i) with hRi_def
  constructor
  ·
    intro hj
    have hmem : ∀ (k : Fin n), k ≤ j → (i, k) ∈ Ri := by
      intro k hk
      simp only [hRi_def]
      apply Finset.mem_filter.mpr
      constructor
      · rcases eq_or_lt_of_le hk with h | h
        · rw [h]; exact hj
        · exact hS i j k hj h
      · rfl
    have hcard : (Finset.Iic j).card ≤ Ri.card := by
      have hf : ∀ k ∈ Finset.Iic j, (fun k => (i, k)) k ∈ Ri :=
        fun k hk => hmem k (Finset.mem_Iic.mp hk)
      have hinj : Set.InjOn (fun k : Fin n => (i, k)) (Finset.Iic j : Set (Fin n)) :=
        fun a _ b _ hab => by simp [Prod.ext_iff] at hab; exact hab
      calc (Finset.Iic j).card
          ≤ ((Finset.Iic j).image (fun k => (i, k))).card := by
            rw [Finset.card_image_of_injOn hinj]
        _ ≤ Ri.card := Finset.card_le_card (by
            intro x hx; simp [Finset.mem_image] at hx
            obtain ⟨k, hk, rfl⟩ := hx; exact hf k (Finset.mem_Iic.mpr hk))
    rw [Fin.card_Iic] at hcard; omega
  ·
    intro hlt
    by_contra hj
    have hnotin : ∀ j' : Fin n, j ≤ j' → (i, j') ∉ S := by
      intro j' hle hmem
      rcases eq_or_lt_of_le hle with heq | hlt'
      · exact hj (heq ▸ hmem)
      · exact hj (hS i j' j hmem hlt')
    have hsub : Ri ⊆ (Finset.Iio j).image (fun k => (i, k)) := by
      intro ⟨a, b⟩ hmem'
      simp only [hRi_def, Finset.mem_filter] at hmem'
      simp only [Finset.mem_image, Finset.mem_Iio]
      exact ⟨b, by_contra (fun hle => hnotin b (not_lt.mp hle) (hmem'.2 ▸ hmem'.1)),
             by simp [hmem'.2]⟩
    have hcard : Ri.card ≤ j.val := by
      calc Ri.card
          ≤ ((Finset.Iio j).image (fun k => (i, k))).card := Finset.card_le_card hsub
        _ ≤ (Finset.Iio j).card := Finset.card_image_le
        _ = j.val := Fin.card_Iio j
    omega

theorem leftJustified_eq_of_rowSize_eq {S T : Finset (Fin m × Fin n)}
    (hS : IsLeftJustified S) (hT : IsLeftJustified T)
    (h : ∀ i, rowSize S i = rowSize T i) : S = T := by
  ext ⟨i, j⟩
  rw [mem_iff_lt_rowSize hS, mem_iff_lt_rowSize hT, h]

lemma map_finRange_pairwise_ge {f : Fin m → ℕ} (hf : Antitone f) :
    ((List.finRange m).map f).Pairwise (· ≥ ·) := by
  rw [List.pairwise_map]
  exact (List.pairwise_le_finRange m).imp (fun hab => hf hab)

lemma univ_val_eq_coe_finRange :
    (Finset.univ : Finset (Fin m)).val = ↑(List.finRange m) := by
  ext x; simp

theorem antitone_eq_of_multiset_eq {f g : Fin m → ℕ} (hf : Antitone f) (hg : Antitone g)
    (h : Finset.univ.val.map f = Finset.univ.val.map g) : f = g := by
  have hpw_f := map_finRange_pairwise_ge hf
  have hpw_g := map_finRange_pairwise_ge hg
  have hmulti : (↑((List.finRange m).map f) : Multiset ℕ) = ↑((List.finRange m).map g) := by
    simp only [← Multiset.map_coe, ← univ_val_eq_coe_finRange, h]
  have hperm := Multiset.coe_eq_coe.mp hmulti
  have heq : (List.finRange m).map f = (List.finRange m).map g :=
    hperm.eq_of_pairwise (fun a b _ _ h1 h2 => le_antisymm h2 h1) hpw_f hpw_g
  funext i
  exact (List.map_eq_map_iff.mp heq) i (List.mem_finRange i)

theorem gridYoung_unique {S T : Finset (Fin m × Fin n)}
    (hS : IsGridYoung S) (hT : IsGridYoung T)
    (h : rowSizeMultiset S = rowSizeMultiset T) : S = T := by
  apply leftJustified_eq_of_rowSize_eq hS.1 hT.1
  exact fun i => congr_fun (antitone_eq_of_multiset_eq hS.2 hT.2 h) i

end WreathOrbits
