/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopClassification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationLoopWalk.Part7
import Def.StatisticalMechanics.Code.Onsager.DecorationLoopClassification


namespace StatMech.Onsager

open Finset SimpleGraph

theorem ons_decChainPathIndices_comm (a b : Fin 4) :
    ons_decChainPathIndices a b = ons_decChainPathIndices b a := by
  ext i
  simp only [ons_decChainPathIndices, Finset.mem_filter,
    Finset.mem_univ, true_and]
  tauto

theorem ons_decLoopExponent_eq_external_add_internal
    (L : ℕ) {n : ℕ} [NeZero n] (d : Fin n → ons_Dart L) :
    ons_decLoopExponent L d =
      ons_decLoopExternalExponent L d +
        ons_decLoopInternalExponent L d := by
  unfold ons_decLoopExponent ons_decTransitionExponent
    ons_decLoopExternalExponent ons_decLoopInternalExponent
  rw [Finset.sum_add_distrib]
  congr 1
  exact Equiv.sum_comp (Equiv.addRight (1 : Fin n))
    (fun k ↦ Finsupp.single s(d k, ons_dartRev L (d k)) 1)

theorem ons_decLoopExponent_rotate
    (L : ℕ) {n : ℕ} [NeZero n]
    (d : Fin n → ons_Dart L) (r : Fin n) :
    ons_decLoopExponent L (ons_rotate r d) =
      ons_decLoopExponent L d := by
  unfold ons_decLoopExponent
  simpa [ons_rotate, add_assoc, add_comm, add_left_comm] using
    Equiv.sum_comp (Equiv.addRight r)
      (fun k : Fin n ↦
        ons_decTransitionExponent L (d k) (d (k + 1)))

theorem ons_decLoopScalar_rotate
    (L : ℕ) [Fact (2 < L)] (omega u v : ℂ)
    {n : ℕ} [NeZero n] (d : Fin n → ons_Dart L) (r : Fin n) :
    ons_decLoopScalar L omega u v (ons_rotate r d) =
      ons_decLoopScalar L omega u v d := by
  rw [ons_decLoopScalar_eq_loopWeight_one,
    ons_decLoopScalar_eq_loopWeight_one]
  exact ons_loopWeight_rotate
    (ons_KWmatWeightedPhase L (fun _ ↦ 1) omega u v) r d

theorem ons_decLoopExternalExponent_loopRev
    (L : ℕ) {n : ℕ} [NeZero n] (d : Fin n → ons_Dart L) :
    ons_decLoopExternalExponent L (ons_loopRev L d) =
      ons_decLoopExternalExponent L d := by
  unfold ons_decLoopExternalExponent ons_loopRev
  calc
    (∑ k : Fin n, Finsupp.single
        s(ons_dartRev L (d (-k)),
          ons_dartRev L (ons_dartRev L (d (-k)))) 1) =
        ∑ k : Fin n, Finsupp.single
          s(d (-k), ons_dartRev L (d (-k))) 1 := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [ons_dartRev_involutive, Sym2.eq_swap]
    _ = ∑ k : Fin n, Finsupp.single
          s(d k, ons_dartRev L (d k)) 1 :=
      Equiv.sum_comp (Equiv.neg (Fin n))
        (fun k ↦ Finsupp.single s(d k, ons_dartRev L (d k)) 1)

theorem ons_decLoopInternalExponent_loopRev
    (L : ℕ) {n : ℕ} [NeZero n] (d : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1) :
    ons_decLoopInternalExponent L (ons_loopRev L d) =
      ons_decLoopInternalExponent L d := by
  unfold ons_decLoopInternalExponent
  let e : Fin n ≃ Fin n :=
    (Equiv.addRight (1 : Fin n)).trans (Equiv.neg (Fin n))
  calc
    (∑ k : Fin n,
      ∑ i ∈ ons_decChainPathIndices
          ((ons_loopRev L d (k + 1)).2 + 2)
          (ons_loopRev L d k).2,
        Finsupp.single
          (ons_decChainEdge (ons_loopRev L d k).1 i) 1) =
        ∑ k : Fin n,
          ∑ i ∈ ons_decChainPathIndices
              ((d (e k + 1)).2 + 2) (d (e k)).2,
            Finsupp.single (ons_decChainEdge (d (e k)).1 i) 1 := by
      apply Finset.sum_congr rfl
      intro k hk
      have he : e k = -(k + 1) := rfl
      rw [he]
      have hidx : -(k + 1) + 1 = -k := by abel
      have hsite := hvalid (-(k + 1))
      rw [hidx] at hsite
      simp only [ons_loopRev, ons_dartRev, Prod.snd, Prod.fst]
      simp only [add_assoc]
      rw [show (2 + 2 : Fin 4) = 0 by decide, add_zero]
      rw [hidx, ← hsite, ons_decChainPathIndices_comm]
    _ = ∑ k : Fin n,
          ∑ i ∈ ons_decChainPathIndices
              ((d (k + 1)).2 + 2) (d k).2,
            Finsupp.single (ons_decChainEdge (d k).1 i) 1 :=
      Equiv.sum_comp e
        (fun k : Fin n ↦
          ∑ i ∈ ons_decChainPathIndices
              ((d (k + 1)).2 + 2) (d k).2,
            Finsupp.single (ons_decChainEdge (d k).1 i) 1)

theorem ons_decLoopExponent_loopRev
    (L : ℕ) {n : ℕ} [NeZero n] (d : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1) :
    ons_decLoopExponent L (ons_loopRev L d) =
      ons_decLoopExponent L d := by
  rw [ons_decLoopExponent_eq_external_add_internal,
    ons_decLoopExponent_eq_external_add_internal,
    ons_decLoopExternalExponent_loopRev,
    ons_decLoopInternalExponent_loopRev L d hvalid]

theorem ons_decLoopScalar_loopRev_spin
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    {n : ℕ} [NeZero n] (d : Fin n → ons_Dart L) :
    ons_decLoopScalar L ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b) (ons_loopRev L d) =
      ons_decLoopScalar L ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b) d := by
  rw [ons_decLoopScalar_eq_loopWeight_one,
    ons_decLoopScalar_eq_loopWeight_one,
    ons_KWmatWeightedPhase_const]
  exact ons_loopWeight_spinPhase_loopRev
    (1 : ℂ) ons_turnRoot ons_turnRoot_sq a b d

end StatMech.Onsager
