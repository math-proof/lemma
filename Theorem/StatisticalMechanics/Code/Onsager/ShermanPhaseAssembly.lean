/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanPhaseAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.KWPhaseLemma5
import Theorem.StatisticalMechanics.Code.Onsager.KWSpectral.Part2
import Def.StatisticalMechanics.Code.Onsager.ShermanPhaseAssembly


namespace StatMech.Onsager

open Matrix BigOperators

theorem ons_KWmatPhase_loopSum_two_bucket
    {L : ℕ} [NeZero L] [Fact (2 < L)] {n : ℕ}
    (x omega : ℂ) (homega : omega ^ 2 = Complex.I)
    (a b : Fin 2) (e : ons_Dart L) :
    (∑ d : Fin (n + 1) → ons_Dart L,
      ons_loopWeight (ons_KWmatPhase L x omega
        (ons_spinPhase L a) (ons_spinPhase L b)) d) =
      2 * ons_phaseBucketE L x omega a b e n +
        ons_phaseBucketN L x omega a b e n := by
  let M := ons_KWmatPhase L x omega
    (ons_spinPhase L a) (ons_spinPhase L b)
  let P : (Fin (n + 1) → ons_Dart L) → Prop := fun d => ∃ i, d i = e
  let Q : (Fin (n + 1) → ons_Dart L) → Prop := fun d =>
    ∃ j, d j = ons_dartRev L e
  have hsplit := ons_sum_split_by_two P Q (fun d => ons_loopWeight M d)
  have hboth := ons_loopSum_spinPhase_both_zero n x omega homega a b e
  have hsymm := ons_loopSum_spinPhase_symm
    (L := L) (n := n + 1) x omega homega a b e
  have hset :
      Finset.univ.filter (fun d : Fin (n + 1) → ons_Dart L =>
        (∃ i, d i = ons_dartRev L e) ∧ ¬ ∃ j, d j = e) =
      Finset.univ.filter (fun d : Fin (n + 1) → ons_Dart L =>
        ¬ (∃ i, d i = e) ∧ ∃ j, d j = ons_dartRev L e) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_comm
  rw [hset] at hsymm
  simp only [P, Q, M] at hsplit
  unfold ons_phaseBucketE ons_phaseBucketN
  linear_combination hsplit + hboth - hsymm

theorem ons_KWmatPhase_mask_loopSum_two_bucket
    {L : ℕ} [NeZero L] [Fact (2 < L)] {n : ℕ}
    (x omega : ℂ) (homega : omega ^ 2 = Complex.I)
    (a b : Fin 2) (forbidden : Finset (ons_Dart L))
    (hforbidden : ∀ d,
      ons_dartRev L d ∈ forbidden ↔ d ∈ forbidden)
    (e : ons_Dart L) :
    (∑ d : Fin (n + 1) → ons_Dart L,
      ons_loopWeight
        (ons_maskMatrix forbidden (ons_KWmatPhase L x omega
          (ons_spinPhase L a) (ons_spinPhase L b))) d) =
      2 * ons_maskPhaseBucketE L x omega a b forbidden e n +
        ons_maskPhaseBucketN L x omega a b forbidden e n := by
  let M := ons_maskMatrix forbidden (ons_KWmatPhase L x omega
    (ons_spinPhase L a) (ons_spinPhase L b))
  let P : (Fin (n + 1) → ons_Dart L) → Prop := fun d => ∃ i, d i = e
  let Q : (Fin (n + 1) → ons_Dart L) → Prop := fun d =>
    ∃ j, d j = ons_dartRev L e
  have hsplit := ons_sum_split_by_two P Q (fun d => ons_loopWeight M d)
  have hboth := ons_loopSum_spinPhase_mask_both_zero
    n x omega homega a b forbidden hforbidden e
  have hsymm := ons_loopSum_spinPhase_mask_symm
    (L := L) (n := n + 1) x omega homega a b
    forbidden hforbidden e
  have hset :
      Finset.univ.filter (fun d : Fin (n + 1) → ons_Dart L =>
        (∃ i, d i = ons_dartRev L e) ∧ ¬ ∃ j, d j = e) =
      Finset.univ.filter (fun d : Fin (n + 1) → ons_Dart L =>
        ¬ (∃ i, d i = e) ∧ ∃ j, d j = ons_dartRev L e) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_comm
  rw [hset] at hsymm
  simp only [P, Q, M] at hsplit
  unfold ons_maskPhaseBucketE ons_maskPhaseBucketN
  linear_combination hsplit + hboth - hsymm

theorem ons_KWmatPhase_det_eq_two_bucket_exp
    {L : ℕ} [NeZero L] [Fact (2 < L)]
    (x omega : ℂ) (homega : omega ^ 2 = Complex.I)
    (a b : Fin 2) (e : ons_Dart L)
    (hspec : ∀ alpha ∈ (ons_KWmatPhase L x omega
      (ons_spinPhase L a) (ons_spinPhase L b)).charpoly.roots,
      ‖alpha‖ < 1) :
    (1 - ons_KWmatPhase L x omega
      (ons_spinPhase L a) (ons_spinPhase L b)).det =
      Complex.exp (-∑' n : ℕ,
        (2 * ons_phaseBucketE L x omega a b e n +
          ons_phaseBucketN L x omega a b e n) / ((n : ℂ) + 1)) := by
  rw [ons_det_eq_walk_exp _ hspec]
  refine congrArg Complex.exp (congrArg Neg.neg (tsum_congr (fun n => ?_)))
  exact congrArg (· / ((n : ℂ) + 1))
    (ons_KWmatPhase_loopSum_two_bucket x omega homega a b e)

theorem ons_KWmatPhase_det_eq_A_mul_bucket
    {L : ℕ} [NeZero L] [Fact (2 < L)]
    (x omega : ℂ) (homega : omega ^ 2 = Complex.I)
    (a b : Fin 2) (e : ons_Dart L)
    (hspec : ∀ alpha ∈ (ons_KWmatPhase L x omega
      (ons_spinPhase L a) (ons_spinPhase L b)).charpoly.roots,
      ‖alpha‖ < 1)
    (hB : Summable (fun n : ℕ =>
      ons_phaseBucketE L x omega a b e n / ((n : ℂ) + 1)))
    (hN : Summable (fun n : ℕ =>
      ons_phaseBucketN L x omega a b e n / ((n : ℂ) + 1))) :
    (1 - ons_KWmatPhase L x omega
      (ons_spinPhase L a) (ons_spinPhase L b)).det =
      Complex.exp (-∑' n : ℕ,
        ons_phaseBucketN L x omega a b e n / ((n : ℂ) + 1)) *
      Complex.exp (-2 * ∑' n : ℕ,
        ons_phaseBucketE L x omega a b e n / ((n : ℂ) + 1)) := by
  have hsplit :
      (∑' n : ℕ, (2 * ons_phaseBucketE L x omega a b e n +
        ons_phaseBucketN L x omega a b e n) / ((n : ℂ) + 1)) =
      2 * (∑' n : ℕ,
        ons_phaseBucketE L x omega a b e n / ((n : ℂ) + 1)) +
      (∑' n : ℕ,
        ons_phaseBucketN L x omega a b e n / ((n : ℂ) + 1)) := by
    have heq : (fun n : ℕ =>
        (2 * ons_phaseBucketE L x omega a b e n +
          ons_phaseBucketN L x omega a b e n) / ((n : ℂ) + 1)) =
        (fun n : ℕ => 2 *
          (ons_phaseBucketE L x omega a b e n / ((n : ℂ) + 1)) +
          ons_phaseBucketN L x omega a b e n / ((n : ℂ) + 1)) := by
      funext n
      ring
    rw [heq, (hB.mul_left 2).tsum_add hN, tsum_mul_left]
  rw [ons_KWmatPhase_det_eq_two_bucket_exp x omega homega a b e hspec,
    hsplit]
  rw [show -(2 * (∑' n : ℕ,
        ons_phaseBucketE L x omega a b e n / ((n : ℂ) + 1)) +
      (∑' n : ℕ,
        ons_phaseBucketN L x omega a b e n / ((n : ℂ) + 1))) =
      (-(∑' n : ℕ,
        ons_phaseBucketN L x omega a b e n / ((n : ℂ) + 1))) +
      (-2 * ∑' n : ℕ,
        ons_phaseBucketE L x omega a b e n / ((n : ℂ) + 1)) by ring,
    Complex.exp_add]

theorem ons_phaseBucketSeries_eq_geometric
    {L : ℕ} [NeZero L] [Fact (2 < L)]
    (x omega : ℂ) (a b : Fin 2) (e : ons_Dart L)
    (hsum : Summable fun s =>
      ‖ons_firstReturnWeight (ons_KWmatPhase L x omega
        (ons_spinPhase L a) (ons_spinPhase L b))
        e (ons_dartRev L e) s‖)
    (hsmall : ∑' s,
      ‖ons_firstReturnWeight (ons_KWmatPhase L x omega
        (ons_spinPhase L a) (ons_spinPhase L b))
        e (ons_dartRev L e) s‖ < 1) :
    (∑' n : ℕ,
      ons_phaseBucketE L x omega a b e n / ((n : ℂ) + 1)) =
      ∑' k : ℕ,
        (∑' s, ons_firstReturnWeight (ons_KWmatPhase L x omega
          (ons_spinPhase L a) (ons_spinPhase L b))
          e (ons_dartRev L e) s) ^ (k + 1) / (k + 1) := by
  have her : e ≠ ons_dartRev L e := (ons_dartRev_ne L e).symm
  simpa only [ons_phaseBucketE, not_exists] using
    ons_loopBucketSeries_eq_geometric
      (ons_KWmatPhase L x omega
        (ons_spinPhase L a) (ons_spinPhase L b))
      e (ons_dartRev L e) her hsum hsmall

theorem ons_summable_phaseBucketE_firstReturn
    {L : ℕ} [NeZero L] [Fact (2 < L)]
    (x omega : ℂ) (a b : Fin 2) (e : ons_Dart L)
    (hsum : Summable fun s =>
      ‖ons_firstReturnWeight (ons_KWmatPhase L x omega
        (ons_spinPhase L a) (ons_spinPhase L b))
        e (ons_dartRev L e) s‖)
    (hsmall : ∑' s,
      ‖ons_firstReturnWeight (ons_KWmatPhase L x omega
        (ons_spinPhase L a) (ons_spinPhase L b))
        e (ons_dartRev L e) s‖ < 1) :
    Summable fun n : ℕ =>
      ons_phaseBucketE L x omega a b e n / ((n : ℂ) + 1) := by
  have her : e ≠ ons_dartRev L e := (ons_dartRev_ne L e).symm
  simpa only [ons_phaseBucketE, not_exists] using
    ons_summable_loopBucketSeries
      (ons_KWmatPhase L x omega
        (ons_spinPhase L a) (ons_spinPhase L b))
      e (ons_dartRev L e) her hsum hsmall

theorem ons_hlam_spinPhase_firstReturn
    {L : ℕ} [NeZero L] [Fact (2 < L)]
    (x omega : ℂ) (a b : Fin 2) (e : ons_Dart L)
    (hsum : Summable fun s =>
      ‖ons_firstReturnWeight (ons_KWmatPhase L x omega
        (ons_spinPhase L a) (ons_spinPhase L b))
        e (ons_dartRev L e) s‖)
    (hsmall : ∑' s,
      ‖ons_firstReturnWeight (ons_KWmatPhase L x omega
        (ons_spinPhase L a) (ons_spinPhase L b))
        e (ons_dartRev L e) s‖ < 1) :
    Complex.exp (-∑' n : ℕ,
      ons_phaseBucketE L x omega a b e n / ((n : ℂ) + 1)) =
      1 - ∑' s, ons_firstReturnWeight (ons_KWmatPhase L x omega
        (ons_spinPhase L a) (ons_spinPhase L b))
        e (ons_dartRev L e) s := by
  let z := ∑' s, ons_firstReturnWeight (ons_KWmatPhase L x omega
    (ons_spinPhase L a) (ons_spinPhase L b))
    e (ons_dartRev L e) s
  have hz : ‖z‖ < 1 :=
    lt_of_le_of_lt (norm_tsum_le_tsum_norm hsum) hsmall
  rw [ons_phaseBucketSeries_eq_geometric x omega a b e hsum hsmall]
  exact ons_lemma4_exp hz

theorem ons_KWmatPhase_spectral_Sherman_small
    (L : ℕ) [NeZero L]
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) (ons_ShermanRadius L))
    (a b : Fin 2) :
    ∀ alpha ∈ (ons_KWmatPhase L (x : ℂ) ons_turnRoot
      (ons_spinPhase L a) (ons_spinPhase L b)).charpoly.roots,
      ‖alpha‖ < 1 := by
  apply ons_KWmatPhase_spectral_lt_one
  exact ons_Sherman_card_mul_small L hx

end StatMech.Onsager
