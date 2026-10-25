/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TwoReplica.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Ising.TwoReplica.Part6
open Finset Classical
open scoped symmDiff BigOperators

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000


namespace StatMech

namespace Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (E : Finset (Sym2 V))


@[simp] lemma reflect_apply (m : Current V) (P : Finset (Sym2 V)) (n : Current V) (e : Sym2 V) :
    reflect m P n e = if e ∈ P then m e - n e else n e := rfl


lemma reflect_le (m : Current V) (P : Finset (Sym2 V)) {n : Current V}
    (hn : ∀ e, n e ≤ m e) : ∀ e, reflect m P n e ≤ m e := by
  intro e; unfold reflect
  by_cases h : e ∈ P
  · simp only [if_pos h]; omega
  · simp only [if_neg h]; exact hn e


lemma reflect_involutive (m : Current V) (P : Finset (Sym2 V)) {n : Current V}
    (hn : ∀ e, n e ≤ m e) : reflect m P (reflect m P n) = n := by
  funext e; unfold reflect
  by_cases h : e ∈ P
  · simp only [if_pos h]; have := hn e; omega
  · simp only [if_neg h]


lemma reflect_add_complement (m : Current V) (P : Finset (Sym2 V)) {n : Current V}
    (hn : ∀ e, n e ≤ m e) (e : Sym2 V) :
    reflect m P n e + reflect m P (fun e => m e - n e) e = m e := by
  unfold reflect
  by_cases h : e ∈ P
  · simp only [if_pos h]; have := hn e; omega
  · simp only [if_neg h]; have := hn e; omega


lemma reflect_complement (m : Current V) (P : Finset (Sym2 V)) (n : Current V) :
    (fun e => m e - reflect m P n e) = reflect m P (fun e => m e - n e) := by
  funext e; unfold reflect
  by_cases h : e ∈ P
  · simp only [if_pos h]
  · simp only [if_neg h]


lemma reflect_parity (m : Current V) (P : Finset (Sym2 V)) (n : Current V)
    (hn : ∀ e, n e ≤ m e) (hodd : ∀ e ∈ P, Odd (m e)) (e : Sym2 V) :
    ((reflect m P n e : ℕ) : ZMod 2)
      = (n e : ZMod 2) + (if e ∈ P then 1 else 0) := by
  unfold reflect
  by_cases h : e ∈ P
  · simp only [if_pos h]
    have hle := hn e
    have key : ((n e : ℕ) : ZMod 2) + ((m e - n e : ℕ) : ZMod 2) = (m e : ZMod 2) := by
      rw [← Nat.cast_add, Nat.add_sub_cancel' hle]
    have hm1 : ((m e : ℕ) : ZMod 2) = 1 := by
      rw [ZMod.natCast_eq_one_iff_odd]; exact hodd e h
    rw [hm1] at key
    have heq : ((m e - n e : ℕ) : ZMod 2) = 1 - (n e : ZMod 2) := by
      rw [eq_sub_iff_add_eq, add_comm]; exact key
    rw [heq, sub_eq_add_neg, CharTwo.neg_eq, add_comm]
  · simp only [if_neg h, add_zero]


lemma degP_as_sum (P : Finset (Sym2 V)) (hP : P ⊆ E) (x : V) :
    degP P x = ∑ e ∈ E.filter (fun e => x ∈ e), (if e ∈ P then 1 else 0) := by
  unfold degP
  rw [Finset.card_eq_sum_ones, ← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext e
  simp only [Finset.mem_filter]
  exact ⟨fun ⟨hP', hx⟩ => ⟨⟨hP hP', hx⟩, hP'⟩, fun ⟨⟨_, hx⟩, hP'⟩ => ⟨hP', hx⟩⟩


lemma flux_reflect_parity (m : Current V) (P : Finset (Sym2 V)) (n : Current V)
    (hn : ∀ e, n e ≤ m e) (hP : P ⊆ E) (hodd : ∀ e ∈ P, Odd (m e)) (x : V) :
    ((incidentFlux E (reflect m P n) x : ℕ) : ZMod 2)
      = ((incidentFlux E n x : ℕ) : ZMod 2) + ((degP P x : ℕ) : ZMod 2) := by
  unfold incidentFlux
  rw [degP_as_sum E P hP x]
  push_cast
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun e he => ?_)
  rw [reflect_parity m P n hn hodd e]


lemma sources_reflect (m : Current V) (P : Finset (Sym2 V)) (n : Current V)
    (hn : ∀ e, n e ≤ m e) (hP : P ⊆ E) (hodd : ∀ e ∈ P, Odd (m e)) :
    sources E (reflect m P n) = sources E n ∆ srcP P := by
  ext x
  simp only [mem_sources, mem_srcP, Finset.mem_symmDiff]
  rw [← ZMod.natCast_eq_one_iff_odd, ← ZMod.natCast_eq_one_iff_odd,
    ← ZMod.natCast_eq_one_iff_odd, flux_reflect_parity E m P n hn hP hodd x]
  generalize ((incidentFlux E n x : ℕ) : ZMod 2) = a
  generalize ((degP P x : ℕ) : ZMod 2) = b
  revert a b; decide


lemma reflect_bijOn (m : Current V) (P : Finset (Sym2 V)) (hP : P ⊆ E)
    (hodd : ∀ e ∈ P, Odd (m e)) (A : Finset V) :
    Set.BijOn (reflect m P)
      {n | (∀ e, n e ≤ m e) ∧ sources E n = A}
      {n | (∀ e, n e ≤ m e) ∧ sources E n = A ∆ srcP P} := by
  refine ⟨?_, ?_, ?_⟩
  · rintro n ⟨hle, hA⟩
    exact ⟨reflect_le m P hle, by rw [sources_reflect E m P n hle hP hodd, hA]⟩
  · rintro n₁ ⟨h1, _⟩ n₂ ⟨h2, _⟩ heq
    have e1 := reflect_involutive m P h1
    have e2 := reflect_involutive m P h2
    rw [← e1, ← e2, heq]
  · rintro L ⟨hLle, hLA⟩
    refine ⟨reflect m P L, ⟨reflect_le m P hLle, ?_⟩, reflect_involutive m P hLle⟩
    rw [sources_reflect E m P L hLle hP hodd, hLA, symmDiff_assoc, symmDiff_self, symmDiff_bot]


end Ising
end StatMech
