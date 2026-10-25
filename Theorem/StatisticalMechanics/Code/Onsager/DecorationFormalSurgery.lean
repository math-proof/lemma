/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalSurgery.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationEdgeClassification
import Def.StatisticalMechanics.Code.Onsager.DecorationFormalSurgery


namespace StatMech.Onsager

open BigOperators Finset

theorem ons_decLoopSetBothExponent_scalar_sum_eq_zero
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    {n : ℕ} [NeZero n] (d : ons_Dart L)
    (m : ons_DecEdge L →₀ ℕ) :
    (∑ loop ∈ ons_decLoopSetBothExponent (n := n) L a b d m,
      ons_decLoopScalar L ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b) loop) = 0 := by
  let Lambda := ons_KWmatWeightedPhase L
    (fun _ : Sym2 (ZMod L × ZMod L) ↦ (1 : ℂ))
    ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)
  have hcancel :
      (∑ loop ∈ ons_decLoopSetBothExponent (n := n) L a b d m,
        ons_loopWeight Lambda loop) = 0 := by
    apply ons_sum_zero_of_sign_involution' Lambda
      (ons_decLoopSetBothExponent (n := n) L a b d m)
      (ons_surgery d (ons_dartRev L))
    · intro loop hmem
      rw [ons_decLoopSetBothExponent, Finset.mem_filter] at hmem ⊢
      have hboth := (ons_mem_loopSetBoth d
        (ons_dartRev L d) loop).1 hmem.1
      have hvalid := ons_decLoop_valid_of_scalar_ne_zero
        L ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)
        loop hmem.2.2
      refine ⟨?_, ?_, ?_⟩
      · apply (ons_mem_loopSetBoth d (ons_dartRev L d) _).2
        exact ons_surgery_visitsBoth (ons_dartRev_involutive L)
          (ons_dartRev_ne L d) hboth
      · rw [ons_decLoopExponent_surgery L d loop hvalid hboth,
          hmem.2.1]
      · rw [ons_decLoopScalar_surgery_sign L ons_turnRoot
          ons_turnRoot_sq a b d loop hboth, neg_ne_zero]
        exact hmem.2.2
    · intro loop hmem
      rw [ons_decLoopSetBothExponent, Finset.mem_filter] at hmem
      have hboth := (ons_mem_loopSetBoth d
        (ons_dartRev L d) loop).1 hmem.1
      simpa only [Lambda] using
        ons_KWmatWeightedPhase_surgery_sign
          (fun _ : Sym2 (ZMod L × ZMod L) ↦ (1 : ℂ))
          ons_turnRoot ons_turnRoot_sq a b d loop
          ((ons_mem_loopSetBoth d (ons_dartRev L d) loop).2 hboth)
    · intro loop hmem
      rw [ons_decLoopSetBothExponent, Finset.mem_filter] at hmem
      have hboth := (ons_mem_loopSetBoth d
        (ons_dartRev L d) loop).1 hmem.1
      exact ons_surgery_involutive (ons_dartRev_involutive L)
        (ons_dartRev_ne L d) hboth
  simpa only [Lambda, ons_decLoopScalar_eq_loopWeight_one] using hcancel

theorem ons_decLoopScalar_sum_both_fixedExponent_eq_zero
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    {n : ℕ} [NeZero n] (d : ons_Dart L)
    (m : ons_DecEdge L →₀ ℕ) :
    (∑ loop ∈ ons_loopSetBoth (n := n) d (ons_dartRev L d),
      if ons_decLoopExponent L loop = m then
        ons_decLoopScalar L ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b) loop
      else 0) = 0 := by
  calc
    (∑ loop ∈ ons_loopSetBoth (n := n) d (ons_dartRev L d),
      if ons_decLoopExponent L loop = m then
        ons_decLoopScalar L ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b) loop
      else 0) =
        ∑ loop ∈ ons_decLoopSetBothExponent (n := n) L a b d m,
          ons_decLoopScalar L ons_turnRoot
            (ons_spinPhase L a) (ons_spinPhase L b) loop := by
      unfold ons_decLoopSetBothExponent
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro loop hloop
      by_cases hexponent : ons_decLoopExponent L loop = m
      · rw [if_pos hexponent]
        by_cases hscalar : ons_decLoopScalar L ons_turnRoot
            (ons_spinPhase L a) (ons_spinPhase L b) loop = 0
        · simp [hscalar]
        · rw [if_pos ⟨hexponent, hscalar⟩]
      · rw [if_neg hexponent, if_neg (fun h :
          ons_decLoopExponent L loop = m ∧
            ons_decLoopScalar L ons_turnRoot
              (ons_spinPhase L a) (ons_spinPhase L b) loop ≠ 0 ↦
          hexponent h.1)]
    _ = 0 := ons_decLoopSetBothExponent_scalar_sum_eq_zero
      (n := n) L a b d m

theorem ons_decFixedExponentTerm_loopRev
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    {n : ℕ} [NeZero n] (m : ons_DecEdge L →₀ ℕ)
    (loop : Fin n → ons_Dart L) :
    (if ons_decLoopExponent L (ons_loopRev L loop) = m then
        ons_decLoopScalar L ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b) (ons_loopRev L loop)
      else 0) =
      if ons_decLoopExponent L loop = m then
        ons_decLoopScalar L ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b) loop
      else 0 := by
  have hscalar := ons_decLoopScalar_loopRev_spin L a b loop
  by_cases hzero : ons_decLoopScalar L ons_turnRoot
      (ons_spinPhase L a) (ons_spinPhase L b) loop = 0
  · rw [hscalar, hzero]
    simp
  · have hvalid := ons_decLoop_valid_of_scalar_ne_zero
      L ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b) loop hzero
    rw [hscalar, ons_decLoopExponent_loopRev L loop hvalid]

theorem ons_decLoopScalar_sum_one_orientation_symm
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    {n : ℕ} [NeZero n] (d : ons_Dart L)
    (m : ons_DecEdge L →₀ ℕ) :
    (∑ loop ∈ Finset.univ.filter (fun loop : Fin n → ons_Dart L ↦
        (∃ k, loop k = d) ∧ ¬ ∃ k, loop k = ons_dartRev L d),
      if ons_decLoopExponent L loop = m then
        ons_decLoopScalar L ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b) loop
      else 0) =
    ∑ loop ∈ Finset.univ.filter (fun loop : Fin n → ons_Dart L ↦
        (∃ k, loop k = ons_dartRev L d) ∧ ¬ ∃ k, loop k = d),
      if ons_decLoopExponent L loop = m then
        ons_decLoopScalar L ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b) loop
      else 0 := by
  refine Finset.sum_nbij' (ons_loopRev L) (ons_loopRev L) ?_ ?_ ?_ ?_ ?_
  · intro loop hloop
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hloop ⊢
    obtain ⟨⟨k, hk⟩, hnot⟩ := hloop
    constructor
    · rw [ons_visits_loopRev, ons_dartRev_involutive L d]
      exact ⟨k, hk⟩
    · rwa [ons_visits_loopRev]
  · intro loop hloop
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hloop ⊢
    obtain ⟨⟨k, hk⟩, hnot⟩ := hloop
    constructor
    · rw [ons_visits_loopRev]
      exact ⟨k, hk⟩
    · rwa [ons_visits_loopRev, ons_dartRev_involutive L d]
  · exact fun loop _ ↦ ons_loopRev_involutive L n loop
  · exact fun loop _ ↦ ons_loopRev_involutive L n loop
  · intro loop hloop
    exact (ons_decFixedExponentTerm_loopRev L a b m loop).symm

end StatMech.Onsager
