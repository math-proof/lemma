/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempSwitching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.HighTempSources.Part3
open Finset
open scoped symmDiff


namespace StatMech

namespace Sharpness

open Ising

variable {V : Type*} [Fintype V] [DecidableEq V]


theorem hasOddBoundary_iff_srcP (F : Finset (Sym2 V)) (A : Finset V) :
    HasOddBoundary F A ↔ srcP F = A := by
  constructor
  · intro h
    ext v
    rw [mem_srcP]
    simpa [incCount, degP] using h v
  · intro h v
    rw [← h, mem_srcP]
    simp [incCount, degP]


theorem hasOddBoundary_symmDiff {F H : Finset (Sym2 V)}
    {A B : Finset V} (hF : HasOddBoundary F A)
    (hH : HasOddBoundary H B) :
    HasOddBoundary (F ∆ H) (A ∆ B) := by
  rw [hasOddBoundary_iff_srcP, srcP_symmDiff,
    (hasOddBoundary_iff_srcP F A).mp hF,
    (hasOddBoundary_iff_srcP H B).mp hH]


theorem mem_symmDiff_singleton_iff {α : Type*} [DecidableEq α]
    (S : Finset α) (a x : α) :
    x ∈ S ∆ {a} ↔ (x ∈ S ↔ x ≠ a) := by
  simp only [Finset.mem_symmDiff, Finset.mem_singleton]
  tauto


theorem card_pair_symmDiff_singleton {α : Type*} [DecidableEq α]
    (F H : Finset α) {e : α} (he : e ∈ F ∆ H) :
    (F ∆ {e}).card + (H ∆ {e}).card = F.card + H.card := by
  simp only [Finset.mem_symmDiff] at he
  by_cases heF : e ∈ F
  · have heH : e ∉ H := by tauto
    rw [show F ∆ {e} = F.erase e by
        ext x
        rw [mem_symmDiff_singleton_iff]
        by_cases hxe : x = e
        · subst x; simp [heF]
        · simp [hxe],
      show H ∆ {e} = insert e H by
        ext x
        rw [mem_symmDiff_singleton_iff]
        by_cases hxe : x = e
        · subst x; simp [heH]
        · simp [hxe],
      card_erase_of_mem heF, card_insert_of_notMem heH]
    have hFpos : 0 < F.card := card_pos.mpr ⟨e, heF⟩
    omega
  · have heH : e ∈ H := by tauto
    rw [show F ∆ {e} = insert e F by
        ext x
        rw [mem_symmDiff_singleton_iff]
        by_cases hxe : x = e
        · subst x; simp [heF]
        · simp [hxe],
      show H ∆ {e} = H.erase e by
        ext x
        rw [mem_symmDiff_singleton_iff]
        by_cases hxe : x = e
        · subst x; simp [heH]
        · simp [hxe],
      card_insert_of_notMem heF, card_erase_of_mem heH]
    have hHpos : 0 < H.card := card_pos.mpr ⟨e, heH⟩
    omega


theorem card_pair_symmDiff_eq {α : Type*} [DecidableEq α]
    (F H Q : Finset α) (hQ : Q ⊆ F ∆ H) :
    (F ∆ Q).card + (H ∆ Q).card = F.card + H.card := by
  induction Q using Finset.induction_on generalizing F H with
  | empty =>
      have hF : F ∆ (∅ : Finset α) = F := by
        ext x
        simp [Finset.mem_symmDiff]
      have hH : H ∆ (∅ : Finset α) = H := by
        ext x
        simp [Finset.mem_symmDiff]
      rw [hF, hH]
  | @insert e Q heQ ih =>
      have heFH : e ∈ F ∆ H := hQ (by simp)
      have hpair : (F ∆ {e}) ∆ (H ∆ {e}) = F ∆ H := by
        ext x
        by_cases hxe : x = e
        · subst x
          simp only [Finset.mem_symmDiff, Finset.mem_singleton]
          tauto
        · simp only [Finset.mem_symmDiff, Finset.mem_singleton]
          simp only [hxe, false_iff, iff_false]
          tauto
      have hQsub : Q ⊆ (F ∆ {e}) ∆ (H ∆ {e}) := by
        intro x hx
        rw [hpair]
        exact hQ (Finset.mem_insert_of_mem hx)
      have hstep := card_pair_symmDiff_singleton F H heFH
      have hrest := ih (F := F ∆ {e}) (H := H ∆ {e}) hQsub
      have hFin : F ∆ insert e Q = (F ∆ {e}) ∆ Q := by
        ext x
        simp only [Finset.mem_symmDiff, Finset.mem_insert,
          Finset.mem_singleton]
        by_cases hxe : x = e
        · subst x
          simp [heQ]
        · by_cases hxQ : x ∈ Q <;> simp [hxe, hxQ] <;> tauto
      have hHin : H ∆ insert e Q = (H ∆ {e}) ∆ Q := by
        ext x
        simp only [Finset.mem_symmDiff, Finset.mem_insert,
          Finset.mem_singleton]
        by_cases hxe : x = e
        · subst x
          simp [heQ]
        · by_cases hxQ : x ∈ Q <;> simp [hxe, hxQ] <;> tauto
      rw [hFin, hHin]
      exact hrest.trans hstep


end Sharpness
end StatMech
