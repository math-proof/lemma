/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalExternal.Part3
import Def.StatisticalMechanics.Code.Onsager.DecorationFormalFirstReturn


namespace StatMech.Onsager

open BigOperators Finset

section GenericReroot

variable {E : Type*} [Fintype E] [DecidableEq E]

variable {n : ℕ} [NeZero n]

theorem ons_invariantMarkedTerm_eq_rerootTerm
    (weight : (Fin n → E) → ℂ)
    (hrotate : ∀ k loop, weight (ons_rotate k loop) = weight loop)
    (e r : E) (k : Fin n) (loop : Fin n → E) :
    ons_invariantMarkedTerm weight e r k loop =
      ons_invariantRerootTerm weight e r (ons_rotate k loop) := by
  unfold ons_invariantMarkedTerm ons_invariantRerootTerm
  by_cases h : (∀ j, loop j ≠ r) ∧ loop k = e
  · rw [if_pos h]
    have hrot : (∀ j, ons_rotate k loop j ≠ r) ∧
        ons_rotate k loop 0 = e :=
      ⟨(ons_avoids_rotate r k loop).2 h.1, by simpa using h.2⟩
    rw [if_pos hrot, hrotate, ons_visitCount_rotate]
  · rw [if_neg h]
    have hrot : ¬ ((∀ j, ons_rotate k loop j ≠ r) ∧
        ons_rotate k loop 0 = e) := by
      intro hr
      apply h
      exact ⟨(ons_avoids_rotate r k loop).1 hr.1, by simpa using hr.2⟩
    rw [if_neg hrot]

theorem ons_sum_invariantMarkedTerm
    (weight : (Fin n → E) → ℂ)
    (hrotate : ∀ k loop, weight (ons_rotate k loop) = weight loop)
    (e r : E) (k : Fin n) :
    ∑ loop : Fin n → E, ons_invariantMarkedTerm weight e r k loop =
      ∑ loop : Fin n → E, ons_invariantRerootTerm weight e r loop := by
  simp_rw [ons_invariantMarkedTerm_eq_rerootTerm weight hrotate]
  exact Equiv.sum_comp (ons_rotateEquiv k)
    (ons_invariantRerootTerm weight e r)

theorem ons_sum_invariantMarks_recovers
    (weight : (Fin n → E) → ℂ) (e r : E) (loop : Fin n → E) :
    (∑ k : Fin n, ons_invariantMarkedTerm weight e r k loop) =
      if (∀ j, loop j ≠ r) ∧ (∃ k, loop k = e) then weight loop else 0 := by
  unfold ons_invariantMarkedTerm
  by_cases hav : ∀ j, loop j ≠ r
  · have hterm : ∀ k : Fin n,
        (if (∀ j, loop j ≠ r) ∧ loop k = e then
            weight loop / (ons_visitCount e loop : ℂ) else 0) =
          if loop k = e then
            weight loop / (ons_visitCount e loop : ℂ) else 0 := by
      intro k
      by_cases hk : loop k = e <;> simp [hav, hk]
    rw [Finset.sum_congr rfl (fun k _ ↦ hterm k)]
    by_cases hvis : ∃ k, loop k = e
    · rw [if_pos ⟨hav, hvis⟩]
      have hcount : 0 < ons_visitCount e loop :=
        (ons_visitCount_pos_iff e loop).2 hvis
      have hcountC : (ons_visitCount e loop : ℂ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt hcount)
      have hsum : (∑ k : Fin n, if loop k = e then (1 : ℂ) else 0) =
          (ons_visitCount e loop : ℂ) := by
        rw [Finset.sum_boole, ons_visitCount_eq_card_filter]
      calc
        (∑ k : Fin n, if loop k = e then
            weight loop / (ons_visitCount e loop : ℂ) else 0) =
            (∑ k : Fin n, if loop k = e then (1 : ℂ) else 0) *
              (weight loop / (ons_visitCount e loop : ℂ)) := by
                rw [Finset.sum_mul]
                apply Finset.sum_congr rfl
                intro k hk
                split_ifs <;> simp
        _ = weight loop := by
          rw [hsum]
          field_simp [hcountC]
    · rw [if_neg (fun h ↦ hvis h.2)]
      push Not at hvis
      simp [hvis]
  · have hcond : ¬ ((∀ j, loop j ≠ r) ∧ ∃ k, loop k = e) := by
      aesop
    rw [if_neg hcond]
    apply Finset.sum_eq_zero
    intro k hk
    rw [if_neg]
    exact fun h ↦ hav h.1

theorem ons_sum_div_length_eq_rerooted_of_invariant
    (weight : (Fin n → E) → ℂ)
    (hrotate : ∀ k loop, weight (ons_rotate k loop) = weight loop)
    (e r : E) :
    (∑ loop ∈ Finset.univ.filter (fun loop : Fin n → E ↦
        (∃ k, loop k = e) ∧ ∀ j, loop j ≠ r), weight loop) / (n : ℂ) =
      ∑ loop ∈ Finset.univ.filter (fun loop : Fin n → E ↦
        loop 0 = e ∧ ∀ j, loop j ≠ r),
        weight loop / (ons_visitCount e loop : ℂ) := by
  have hn : (n : ℂ) ≠ 0 := by
    exact_mod_cast NeZero.ne n
  have hdouble :
      (∑ loop : Fin n → E,
        ∑ k : Fin n, ons_invariantMarkedTerm weight e r k loop) =
        (n : ℂ) * ∑ loop : Fin n → E,
          ons_invariantRerootTerm weight e r loop := by
    rw [Finset.sum_comm]
    simp_rw [ons_sum_invariantMarkedTerm weight hrotate]
    simp
  have hleft :
      (∑ loop : Fin n → E,
        ∑ k : Fin n, ons_invariantMarkedTerm weight e r k loop) =
        ∑ loop ∈ Finset.univ.filter (fun loop : Fin n → E ↦
          (∃ k, loop k = e) ∧ ∀ j, loop j ≠ r), weight loop := by
    simp_rw [ons_sum_invariantMarks_recovers]
    rw [Finset.sum_ite]
    simp only [Finset.sum_const_zero, add_zero]
    apply Finset.sum_congr
    · ext loop
      simp [and_comm]
    · simp
  have hright :
      (∑ loop : Fin n → E, ons_invariantRerootTerm weight e r loop) =
        ∑ loop ∈ Finset.univ.filter (fun loop : Fin n → E ↦
          loop 0 = e ∧ ∀ j, loop j ≠ r),
          weight loop / (ons_visitCount e loop : ℂ) := by
    unfold ons_invariantRerootTerm
    rw [Finset.sum_ite]
    simp only [Finset.sum_const_zero, add_zero]
    apply Finset.sum_congr
    · ext loop
      simp [and_comm]
    · simp
  rw [hleft, hright] at hdouble
  apply (div_eq_iff hn).2
  simpa [mul_comm] using hdouble

end GenericReroot

theorem ons_decFixedExponentTerm_rotate
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    {n : ℕ} [NeZero n] (m : ons_DecEdge L →₀ ℕ)
    (k : Fin n) (loop : Fin n → ons_Dart L) :
    (if ons_decLoopExponent L (ons_rotate k loop) = m then
        ons_decLoopScalar L ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b) (ons_rotate k loop)
      else 0) =
      if ons_decLoopExponent L loop = m then
        ons_decLoopScalar L ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b) loop
      else 0 := by
  rw [ons_decLoopExponent_rotate, ons_decLoopScalar_rotate]

theorem ons_decFormalFixedBucketE_div_eq_rerooted
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    (d : ons_Dart L) (r : ℕ) (m : ons_DecEdge L →₀ ℕ) :
    ons_decFormalFixedBucketE L a b d r m / ((r : ℂ) + 1) =
      ∑ loop ∈ Finset.univ.filter
          (fun loop : Fin (r + 1) → ons_Dart L ↦
            loop 0 = d ∧ ∀ j, loop j ≠ ons_dartRev L d),
        (if ons_decLoopExponent L loop = m then
            ons_decLoopScalar L ons_turnRoot
              (ons_spinPhase L a) (ons_spinPhase L b) loop
          else 0) / (ons_visitCount d loop : ℂ) := by
  let weight : (Fin (r + 1) → ons_Dart L) → ℂ := fun loop ↦
    if ons_decLoopExponent L loop = m then
      ons_decLoopScalar L ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b) loop
    else 0
  have hreroot := ons_sum_div_length_eq_rerooted_of_invariant weight
    (fun k loop ↦ ons_decFixedExponentTerm_rotate L a b m k loop)
    d (ons_dartRev L d)
  unfold ons_decFormalFixedBucketE
  simpa only [weight, Nat.cast_add, Nat.cast_one, not_exists] using hreroot

end StatMech.Onsager
