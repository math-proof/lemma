/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wnuupperhalf.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.GaussBonnet.Part4
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WindingWitness.Part4
import Theorem.StatisticalMechanics.Code.Walls.umffullrev.Part2
import Theorem.StatisticalMechanics.Code.Walls.wndwinding.Part3
import Def.StatisticalMechanics.Code.Walls.wnuupperhalf
open Finset Set SimpleGraph
open scoped BigOperators


namespace StatMech

namespace Lattice

@[simp] theorem wnu_Alt_nil : wnu_Alt [] := trivial

@[simp] theorem wnu_Alt_singleton (a : ℤ) : wnu_Alt [a] ↔ (a = 1 ∨ a = -1) := Iff.rfl

theorem wnu_Alt_cons_cons {a b : ℤ} {t : List ℤ} :
    wnu_Alt (a :: b :: t) ↔ (a = 1 ∨ a = -1) ∧ b = -a ∧ wnu_Alt (b :: t) := Iff.rfl


theorem wnu_Alt_tail {a : ℤ} {t : List ℤ} (h : wnu_Alt (a :: t)) : wnu_Alt t := by
  cases t with
  | nil => exact trivial
  | cons b t' => exact (wnu_Alt_cons_cons.mp h).2.2


theorem wnu_Alt_head_pm {a : ℤ} {t : List ℤ} (h : wnu_Alt (a :: t)) : a = 1 ∨ a = -1 := by
  cases t with
  | nil => exact h
  | cons b t' => exact (wnu_Alt_cons_cons.mp h).1


theorem wnu_altSum_mem : ∀ (L : List ℤ), wnu_Alt L →
    (L.sum = 0 ∨ (∃ s, (s = 1 ∨ s = -1) ∧ L.sum = s)) := by
  intro L
  induction L using List.twoStepInduction with
  | nil => intro _; left; simp
  | singleton a =>
    intro h
    right
    exact ⟨a, h, by simp⟩
  | cons_cons a b t ih _ =>
    intro h
    have hb : b = -a := (wnu_Alt_cons_cons.mp h).2.1
    have htail : wnu_Alt t := wnu_Alt_tail (wnu_Alt_tail h)
    have hsum : (a :: b :: t).sum = t.sum := by
      simp only [List.sum_cons, hb]; ring
    rcases ih htail with h0 | ⟨s, hs, hseq⟩
    · left; rw [hsum, h0]
    · right; exact ⟨s, hs, by rw [hsum, hseq]⟩


theorem wnu_altSum_abs_le_one (L : List ℤ) (h : wnu_Alt L) : |L.sum| ≤ 1 := by
  rcases wnu_altSum_mem L h with h0 | ⟨s, hs, hseq⟩
  · rw [h0]; decide
  · rw [hseq]; rcases hs with rfl | rfl <;> decide


theorem wnu_altSum_pm_one_of_ne_zero (L : List ℤ) (h : wnu_Alt L) (hne : L.sum ≠ 0) :
    L.sum = 1 ∨ L.sum = -1 := by
  rcases wnu_altSum_mem L h with h0 | ⟨s, hs, hseq⟩
  · exact absurd h0 hne
  · rw [hseq]; exact hs


theorem wnu_sum_filter_ne_zero (L : List ℤ) :
    L.sum = (L.filter (fun s => s ≠ 0)).sum := by
  classical
  induction L with
  | nil => simp
  | cons a t ih =>
    by_cases ha : a = 0
    · rw [List.filter_cons_of_neg (by simp [ha]), List.sum_cons, ha, zero_add, ih]
    · rw [List.filter_cons_of_pos (by simp [ha]), List.sum_cons, List.sum_cons, ih]


theorem wnu_signedCross_eq_filter_sum (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) :
    wnd_signedCross z w =
      ((w.darts.map (fun d => wnd_signStep z d.toProd.1 d.toProd.2)).filter
        (fun s => s ≠ 0)).sum := by
  classical
  unfold wnd_signedCross
  exact wnu_sum_filter_ne_zero _


end Lattice
end StatMech
