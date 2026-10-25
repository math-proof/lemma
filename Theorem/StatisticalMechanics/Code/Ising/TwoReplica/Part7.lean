/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TwoReplica.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Instance.StatisticalMechanics.Code.Ising.TwoReplica
open Finset Classical
open scoped symmDiff BigOperators

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000


namespace StatMech

namespace Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (E : Finset (Sym2 V))


theorem connOdd_of_sources (m : Current V) (hnd : ∀ e ∈ E, ¬ e.IsDiag)
    {u v : V} (huv : u ≠ v) (hsrc : sources E m = {u, v}) :
    connP (oddEdges E m) u v := by
  have hPnd : ∀ e ∈ oddEdges E m, ¬ e.IsDiag := fun e he => hnd e (oddEdges_subset E m he)
  have hbdsrc : srcP (oddEdges E m) = {u, v} := by rw [srcP_oddEdges]; exact hsrc
  refine path_exists (oddEdges E m) hPnd u v ?_ ?_ huv
  · have : u ∈ srcP (oddEdges E m) := by rw [hbdsrc]; simp
    rwa [mem_srcP] at this
  · intro x hx
    have : x ∈ srcP (oddEdges E m) := by rw [mem_srcP]; exact hx
    rw [hbdsrc] at this; simpa using this


theorem ising_switching_lemma (m : Current V)
    {u v : V} (huv : u ≠ v) (hconn : connP (oddEdges E m) u v) (A : Finset V) :
    Nat.card {n : Current V // (∀ e, n e ≤ m e) ∧ sources E n = A ∆ {u, v}}
      = Nat.card {n : Current V // (∀ e, n e ≤ m e) ∧ sources E n = A} := by
  
  obtain ⟨P, hPodd, hPsrc⟩ := exists_conn_set (oddEdges E m) hconn huv
  have hPE : P ⊆ E := hPodd.trans (oddEdges_subset E m)
  have hPoddE : ∀ e ∈ P, Odd (m e) := by
    intro e he
    have := hPodd he; rw [oddEdges, Finset.mem_filter] at this; exact this.2
  
  have hbij := reflect_bijOn E m P hPE hPoddE A
  rw [hPsrc] at hbij
  
  have hcard := Nat.card_congr (hbij.equiv (reflect m P))
  
  have hL : Nat.card {n : Current V // (∀ e, n e ≤ m e) ∧ sources E n = A ∆ {u, v}}
      = Nat.card ({n | (∀ e, n e ≤ m e) ∧ sources E n = A ∆ {u, v}} : Set (Current V)) :=
    Nat.card_congr (Equiv.refl _)
  have hR : Nat.card {n : Current V // (∀ e, n e ≤ m e) ∧ sources E n = A}
      = Nat.card ({n | (∀ e, n e ≤ m e) ∧ sources E n = A} : Set (Current V)) :=
    Nat.card_congr (Equiv.refl _)
  rw [hL, hR, ← hcard]


theorem ising_switching_lemma_pair (n₁ n₂ : Current V)
    {u v : V} (huv : u ≠ v)
    (hconn : connP (oddEdges E (fun e => n₁ e + n₂ e)) u v) (A : Finset V) :
    Nat.card {n : Current V //
        (∀ e, n e ≤ n₁ e + n₂ e) ∧ sources E n = A ∆ {u, v}}
      = Nat.card {n : Current V //
        (∀ e, n e ≤ n₁ e + n₂ e) ∧ sources E n = A} :=
  ising_switching_lemma E (fun e => n₁ e + n₂ e) huv hconn A


theorem ising_switching_sourceless (m : Current V) (hnd : ∀ e ∈ E, ¬ e.IsDiag)
    {u v : V} (huv : u ≠ v) (hsrc : sources E m = {u, v}) :
    Nat.card {n : Current V // (∀ e, n e ≤ m e) ∧ sources E n = {u, v}}
      = Nat.card {n : Current V // (∀ e, n e ≤ m e) ∧ sources E n = ∅} := by
  have hconn := connOdd_of_sources E m hnd huv hsrc
  have h := ising_switching_lemma E m huv hconn ∅
  
  rwa [show (∅ : Finset V) ∆ {u, v} = {u, v} from symmDiff_eq_right.mpr rfl] at h

end Ising
end StatMech
