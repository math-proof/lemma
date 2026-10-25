/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeWilsonAffine.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeIsingAdapter
import Instance.StatisticalMechanics.Code.FrontierA.Z2GaugeWilsonAffine
open scoped symmDiff
open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false


namespace StatMech.FrontierA

variable {E P V : Type*} [Fintype E] [DecidableEq E]
  [Fintype P] [DecidableEq P] [Fintype V] [DecidableEq V]

theorem plaquetteIncidenceCount_eq_filter_card
    (incidence : P → Finset E) (A : Finset P) (e : E) :
    plaquetteIncidenceCount incidence A e =
      (A.filter fun p => e ∈ incidence p).card := by
  unfold plaquetteIncidenceCount
  rw [card_eq_sum_ones, sum_filter]


theorem filter_symmDiff_eq
    (A B : Finset P) (q : P → Prop) [DecidablePred q] :
    (A ∆ B).filter q = A.filter q ∆ B.filter q := by
  ext p
  simp only [mem_filter, mem_symmDiff]
  tauto


theorem card_symmDiff_add_twice_inter (A B : Finset P) :
    (A ∆ B).card + 2 * (A ∩ B).card = A.card + B.card := by
  rw [symmDiff_def]
  change ((A \ B) ∪ (B \ A)).card + 2 * (A ∩ B).card = A.card + B.card
  rw [card_union_of_disjoint]
  · rw [card_sdiff, card_sdiff]
    have hA := card_le_card (inter_subset_left : A ∩ B ⊆ A)
    have hB := card_le_card (inter_subset_right : A ∩ B ⊆ B)
    simp only [inter_comm B A]
    omega
  · rw [disjoint_left]
    intro p hpA hpB
    simp only [mem_sdiff] at hpA hpB
    exact hpA.2 hpB.1


theorem even_plaquetteIncidenceCount_symmDiff_iff
    (incidence : P → Finset E) (A B : Finset P) (e : E) :
    Even (plaquetteIncidenceCount incidence (A ∆ B) e) ↔
      (Even (plaquetteIncidenceCount incidence A e) ↔
        Even (plaquetteIncidenceCount incidence B e)) := by
  rw [plaquetteIncidenceCount_eq_filter_card,
    plaquetteIncidenceCount_eq_filter_card,
    plaquetteIncidenceCount_eq_filter_card,
    filter_symmDiff_eq]
  let X := A.filter fun p => e ∈ incidence p
  let Y := B.filter fun p => e ∈ incidence p
  have hcard := card_symmDiff_add_twice_inter X Y
  have htwo : Even (2 * (X ∩ Y).card) := ⟨(X ∩ Y).card, by omega⟩
  constructor
  · intro hdiff
    have hsum : Even (X.card + Y.card) := by
      rw [← hcard]
      exact hdiff.add htwo
    exact Nat.even_add.mp hsum
  · intro hsame
    have hsum : Even (X.card + Y.card) := Nat.even_add.mpr hsame
    have hdiffPlus : Even ((X ∆ Y).card + 2 * (X ∩ Y).card) := by
      rw [hcard]
      exact hsum
    exact (Nat.even_add.mp hdiffPlus).mpr htwo


theorem mem_gaugeClosedSurfaceFamily_iff
    (incidence : P → Finset E) (A : Finset P) :
    A ∈ gaugeClosedSurfaceFamily incidence ↔
      IsClosedPlaquetteSet incidence A := by
  unfold gaugeClosedSurfaceFamily
  simp


theorem mem_gaugeWilsonSurfaceFamily_iff
    (incidence : P → Finset E) (L : Finset E) (A : Finset P) :
    A ∈ gaugeWilsonSurfaceFamily incidence L ↔
      HasWilsonBoundary incidence A L := by
  unfold gaugeWilsonSurfaceFamily
  simp


theorem hasWilsonBoundary_iff_symmDiff_closed
    (incidence : P → Finset E) (L : Finset E) (D A : Finset P)
    (hD : HasWilsonBoundary incidence D L) :
    HasWilsonBoundary incidence A L ↔
      IsClosedPlaquetteSet incidence (A ∆ D) := by
  have hparity : HasWilsonBoundary incidence A L ↔
      ∀ e, Even (plaquetteIncidenceCount incidence A e) ↔
        Even (plaquetteIncidenceCount incidence D e) := by
    constructor
    · intro hA e
      have hAe := hA e
      have hDe := hD e
      by_cases he : e ∈ L
      · simp only [he, if_true, Nat.even_add_one] at hAe hDe
        tauto
      · simp only [he, if_false, add_zero] at hAe hDe
        tauto
    · intro hsame e
      have hDe := hD e
      have hsameE := hsame e
      by_cases he : e ∈ L
      · simp only [he, if_true, Nat.even_add_one] at hDe ⊢
        tauto
      · simp only [he, if_false, add_zero] at hDe ⊢
        tauto
  rw [hparity]
  unfold IsClosedPlaquetteSet
  constructor
  · intro hsame e
    exact (even_plaquetteIncidenceCount_symmDiff_iff incidence A D e).2
      (hsame e)
  · intro hclosed e
    exact (even_plaquetteIncidenceCount_symmDiff_iff incidence A D e).1
      (hclosed e)


end StatMech.FrontierA
